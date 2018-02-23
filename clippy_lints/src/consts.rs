#![allow(cast_possible_truncation)]

use rustc::lint::LateContext;
use rustc::hir::def::Def;
use rustc::hir::*;
use rustc::ty::{self, Ty, TyCtxt, Instance, layout};
use rustc::ty::subst::{Subst, Substs};
use std::cmp::Ordering::{self, Equal};
use std::cmp::PartialOrd;
use std::hash::{Hash, Hasher};
use std::mem;
use std::rc::Rc;
use syntax::ast::{FloatTy, LitKind, StrStyle};
use syntax::ptr::P;
use syntax::attr;
use rustc::middle::const_val::ConstVal;

#[derive(Debug, Copy, Clone)]
pub enum FloatWidth {
    F32,
    F64,
    Any,
}

impl From<FloatTy> for FloatWidth {
    fn from(ty: FloatTy) -> Self {
        match ty {
            FloatTy::F32 => FloatWidth::F32,
            FloatTy::F64 => FloatWidth::F64,
        }
    }
}

/// A `LitKind`-like enum to fold constant `Expr`s into.
#[derive(Debug, Clone)]
pub enum Constant {
    /// a String "abc"
    Str(String, StrStyle),
    /// a Binary String b"abc"
    Binary(Rc<Vec<u8>>),
    /// a single char 'a'
    Char(char),
    /// an integer's bit representation
    Int(u128),
    /// an f32
    F32(f32),
    /// an f64
    F64(f64),
    /// true or false
    Bool(bool),
    /// an array of constants
    Vec(Vec<Constant>),
    /// also an array, but with only one constant, repeated N times
    Repeat(Box<Constant>, u64),
    /// a tuple of constants
    Tuple(Vec<Constant>),
}

impl PartialEq for Constant {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (&Constant::Str(ref ls, ref l_sty), &Constant::Str(ref rs, ref r_sty)) => ls == rs && l_sty == r_sty,
            (&Constant::Binary(ref l), &Constant::Binary(ref r)) => l == r,
            (&Constant::Char(l), &Constant::Char(r)) => l == r,
            (&Constant::Int(l), &Constant::Int(r)) => l == r,
            (&Constant::F64(l), &Constant::F64(r)) => {
                // we want `Fw32 == FwAny` and `FwAny == Fw64`, by transitivity we must have
                // `Fw32 == Fw64` so don’t compare them
                // mem::transmute is required to catch non-matching 0.0, -0.0, and NaNs
                unsafe { mem::transmute::<f64, u64>(l) == mem::transmute::<f64, u64>(r) }
            },
            (&Constant::F32(l), &Constant::F32(r)) => {
                // we want `Fw32 == FwAny` and `FwAny == Fw64`, by transitivity we must have
                // `Fw32 == Fw64` so don’t compare them
                // mem::transmute is required to catch non-matching 0.0, -0.0, and NaNs
                unsafe { mem::transmute::<f64, u64>(l as f64) == mem::transmute::<f64, u64>(r as f64) }
            },
            (&Constant::Bool(l), &Constant::Bool(r)) => l == r,
            (&Constant::Vec(ref l), &Constant::Vec(ref r)) | (&Constant::Tuple(ref l), &Constant::Tuple(ref r)) => l == r,
            (&Constant::Repeat(ref lv, ref ls), &Constant::Repeat(ref rv, ref rs)) => ls == rs && lv == rv,
            _ => false, // TODO: Are there inter-type equalities?
        }
    }
}

impl Hash for Constant {
    fn hash<H>(&self, state: &mut H)
    where
        H: Hasher,
    {
        match *self {
            Constant::Str(ref s, ref k) => {
                s.hash(state);
                k.hash(state);
            },
            Constant::Binary(ref b) => {
                b.hash(state);
            },
            Constant::Char(c) => {
                c.hash(state);
            },
            Constant::Int(i) => {
                i.hash(state);
            },
            Constant::F32(f) => {
                unsafe { mem::transmute::<f64, u64>(f as f64) }.hash(state);
            },
            Constant::F64(f) => {
                unsafe { mem::transmute::<f64, u64>(f) }.hash(state);
            },
            Constant::Bool(b) => {
                b.hash(state);
            },
            Constant::Vec(ref v) | Constant::Tuple(ref v) => {
                v.hash(state);
            },
            Constant::Repeat(ref c, l) => {
                c.hash(state);
                l.hash(state);
            },
        }
    }
}

impl PartialOrd for Constant {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (&Constant::Str(ref ls, ref l_sty), &Constant::Str(ref rs, ref r_sty)) => if l_sty == r_sty {
                Some(ls.cmp(rs))
            } else {
                None
            },
            (&Constant::Char(ref l), &Constant::Char(ref r)) => Some(l.cmp(r)),
            (&Constant::Int(l), &Constant::Int(r)) => Some(l.cmp(&r)),
            (&Constant::F64(l), &Constant::F64(r)) => l.partial_cmp(&r),
            (&Constant::F32(l), &Constant::F32(r)) => l.partial_cmp(&r),
            (&Constant::Bool(ref l), &Constant::Bool(ref r)) => Some(l.cmp(r)),
            (&Constant::Tuple(ref l), &Constant::Tuple(ref r)) | (&Constant::Vec(ref l), &Constant::Vec(ref r)) => {
                l.partial_cmp(r)
            },
            (&Constant::Repeat(ref lv, ref ls), &Constant::Repeat(ref rv, ref rs)) => match lv.partial_cmp(rv) {
                Some(Equal) => Some(ls.cmp(rs)),
                x => x,
            },
            _ => None, // TODO: Are there any useful inter-type orderings?
        }
    }
}

/// parse a `LitKind` to a `Constant`
#[allow(cast_possible_wrap)]
pub fn lit_to_constant<'a, 'tcx>(lit: &LitKind, tcx: TyCtxt<'a, 'tcx, 'tcx>, mut ty: Ty<'tcx>) -> Constant {
    use syntax::ast::*;
    use rustc::ty::util::IntTypeExt;

    if let ty::TyAdt(adt, _) = ty.sty {
        if adt.is_enum() {
            ty = adt.repr.discr_type().to_ty(tcx)
        }
    }
    match *lit {
        LitKind::Str(ref is, style) => Constant::Str(is.to_string(), style),
        LitKind::Byte(b) => Constant::Int(b as u128),
        LitKind::ByteStr(ref s) => Constant::Binary(Rc::clone(s)),
        LitKind::Char(c) => Constant::Char(c),
        LitKind::Int(n, _) => Constant::Int(n),
        LitKind::Float(ref is, _) |
        LitKind::FloatUnsuffixed(ref is) => match ty.sty {
            ty::TyFloat(FloatTy::F32) => Constant::F32(is.as_str().parse().unwrap()),
            ty::TyFloat(FloatTy::F64) => Constant::F64(is.as_str().parse().unwrap()),
            _ => bug!(),
        },
        LitKind::Bool(b) => Constant::Bool(b),
    }
}

fn constant_not(o: &Constant) -> Option<Constant> {
    use self::Constant::*;
    match *o {
        Bool(b) => Some(Bool(!b)),
        Int(value) => Some(Int(!value)),
        _ => None,
    }
}

fn constant_negate(o: Constant) -> Option<Constant> {
    use self::Constant::*;
    match o {
        Int(value) => (value as i128).checked_neg().map(|n| Int(n as u128)),
        F32(f) => Some(F32(-f)),
        F64(f) => Some(F64(-f)),
        _ => None,
    }
}

pub fn constant(lcx: &LateContext, e: &Expr) -> Option<(Constant, bool)> {
    let mut cx = ConstEvalLateContext {
        tcx: lcx.tcx,
        tables: lcx.tables,
        param_env: lcx.param_env,
        needed_resolution: false,
        substs: lcx.tcx.intern_substs(&[]),
    };
    cx.expr(e).map(|cst| (cst, cx.needed_resolution))
}

pub fn constant_simple(lcx: &LateContext, e: &Expr) -> Option<Constant> {
    constant(lcx, e).and_then(|(cst, res)| if res { None } else { Some(cst) })
}

/// Creates a ConstEvalLateContext from the given LateContext and TypeckTables
pub fn constant_context<'c, 'cc>(lcx: &LateContext<'c, 'cc>, tables: &'cc ty::TypeckTables<'cc>) -> ConstEvalLateContext<'c, 'cc> {
    ConstEvalLateContext {
        tcx: lcx.tcx,
        tables,
        param_env: lcx.param_env,
        needed_resolution: false,
        substs: lcx.tcx.intern_substs(&[]),
    }
}

pub struct ConstEvalLateContext<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    tables: &'a ty::TypeckTables<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    needed_resolution: bool,
    substs: &'tcx Substs<'tcx>,
}

impl<'c, 'cc> ConstEvalLateContext<'c, 'cc> {
    /// simple constant folding: Insert an expression, get a constant or none.
    pub fn expr(&mut self, e: &Expr) -> Option<Constant> {
        match e.node {
            ExprPath(ref qpath) => self.fetch_path(qpath, e.hir_id),
            ExprBlock(ref block) => self.block(block),
            ExprIf(ref cond, ref then, ref otherwise) => self.ifthenelse(cond, then, otherwise),
            ExprLit(ref lit) => Some(lit_to_constant(&lit.node, self.tcx, self.tables.expr_ty(e))),
            ExprArray(ref vec) => self.multi(vec).map(Constant::Vec),
            ExprTup(ref tup) => self.multi(tup).map(Constant::Tuple),
            ExprRepeat(ref value, _) => {
                let n = match self.tables.expr_ty(e).sty {
                    ty::TyArray(_, n) => n.val.to_raw_bits().expect("array length"),
                    _ => span_bug!(e.span, "typeck error"),
                };
                self.expr(value).map(|v| Constant::Repeat(Box::new(v), n as u64))
            },
            ExprUnary(op, ref operand) => self.expr(operand).and_then(|o| match op {
                UnNot => constant_not(&o),
                UnNeg => constant_negate(o),
                UnDeref => Some(o),
            }),
            ExprBinary(op, ref left, ref right) => self.binop(op, left, right),
            // TODO: add other expressions
            _ => None,
        }
    }

    /// create `Some(Vec![..])` of all constants, unless there is any
    /// non-constant part
    fn multi(&mut self, vec: &[Expr]) -> Option<Vec<Constant>> {
        vec.iter()
            .map(|elem| self.expr(elem))
            .collect::<Option<_>>()
    }

    /// lookup a possibly constant expression from a ExprPath
    fn fetch_path(&mut self, qpath: &QPath, id: HirId) -> Option<Constant> {
        let def = self.tables.qpath_def(qpath, id);
        match def {
            Def::Const(def_id) | Def::AssociatedConst(def_id) => {
                let substs = self.tables.node_substs(id);
                let substs = if self.substs.is_empty() {
                    substs
                } else {
                    substs.subst(self.tcx, self.substs)
                };
                let instance = Instance::resolve(self.tcx, self.param_env, def_id, substs)?;
                let gid = GlobalId {
                    instance,
                    promoted: None,
                };
                use rustc::mir::interpret::{GlobalId, Value, PrimVal};
                let result = self.tcx.const_eval(self.param_env.and(gid)).ok()?;
                let ret = match result.val {
                    ConstVal::Value(Value::ByVal(PrimVal::Bytes(b))) => match result.ty.sty {
                        ty::TyUint(_) => Some(Constant::Int(b)),
                        ty::TyInt(ity) => {
                            let bits = layout::Integer::from_attr(self.tcx, attr::IntType::SignedInt(ity)).size().bits();
                            let amt = 128 - bits;
                            // sign extend
                            let b = ((b as i128) << amt) >> amt;
                            Some(Constant::Int(b as u128))
                        },
                        ty::TyFloat(FloatTy::F32) => Some(Constant::F32(f32::from_bits(b as u32))),
                        ty::TyFloat(FloatTy::F64) => Some(Constant::F64(f64::from_bits(b as u64))),
                        // FIXME: implement other conversion
                        _ => None,
                    },
                    // FIXME: implement other conversions
                    _ => None,
                };
                if ret.is_some() {
                    self.needed_resolution = true;
                }
                return ret;
            },
            _ => {},
        }
        None
    }

    /// A block can only yield a constant if it only has one constant expression
    fn block(&mut self, block: &Block) -> Option<Constant> {
        if block.stmts.is_empty() {
            block.expr.as_ref().and_then(|b| self.expr(b))
        } else {
            None
        }
    }

    fn ifthenelse(&mut self, cond: &Expr, then: &P<Expr>, otherwise: &Option<P<Expr>>) -> Option<Constant> {
        if let Some(Constant::Bool(b)) = self.expr(cond) {
            if b {
                self.expr(&**then)
            } else {
                otherwise.as_ref().and_then(|expr| self.expr(expr))
            }
        } else {
            None
        }
    }

    fn binop(&mut self, op: BinOp, left: &Expr, right: &Expr) -> Option<Constant> {
        let l = self.expr(left)?;
        let r = self.expr(right);
        match (l, r) {
            (Constant::Int(l), Some(Constant::Int(r))) => {
                if self.tables.expr_ty(left).is_signed() {
                    let l = l as i128;
                    let r = r as i128;
                    match op.node {
                        BiAdd => l.checked_add(r).map(|n| Constant::Int(n as u128)),
                        BiSub => l.checked_sub(r).map(|n| Constant::Int(n as u128)),
                        BiMul => l.checked_mul(r).map(|n| Constant::Int(n as u128)),
                        BiDiv if r != 0 => l.checked_div(r).map(|n| Constant::Int(n as u128)),
                        BiRem if r != 0 => l.checked_rem(r).map(|n| Constant::Int(n as u128)),
                        BiShr => l.checked_shr(r as u128 as u32).map(|n| Constant::Int(n as u128)),
                        BiShl => l.checked_shl(r as u128 as u32).map(|n| Constant::Int(n as u128)),
                        BiBitXor => Some(Constant::Int((l ^ r) as u128)),
                        BiBitOr => Some(Constant::Int((l | r) as u128)),
                        BiBitAnd => Some(Constant::Int((l & r) as u128)),
                        BiEq => Some(Constant::Bool(l == r)),
                        BiNe => Some(Constant::Bool(l != r)),
                        BiLt => Some(Constant::Bool(l < r)),
                        BiLe => Some(Constant::Bool(l <= r)),
                        BiGe => Some(Constant::Bool(l >= r)),
                        BiGt => Some(Constant::Bool(l > r)),
                        _ => None,
                    }
                } else {
                    match op.node {
                        BiAdd => l.checked_add(r).map(Constant::Int),
                        BiSub => l.checked_sub(r).map(Constant::Int),
                        BiMul => l.checked_mul(r).map(Constant::Int),
                        BiDiv => l.checked_div(r).map(Constant::Int),
                        BiRem => l.checked_rem(r).map(Constant::Int),
                        BiShr => l.checked_shr(r as u32).map(Constant::Int),
                        BiShl => l.checked_shl(r as u32).map(Constant::Int),
                        BiBitXor => Some(Constant::Int(l ^ r)),
                        BiBitOr => Some(Constant::Int(l | r)),
                        BiBitAnd => Some(Constant::Int(l & r)),
                        BiEq => Some(Constant::Bool(l == r)),
                        BiNe => Some(Constant::Bool(l != r)),
                        BiLt => Some(Constant::Bool(l < r)),
                        BiLe => Some(Constant::Bool(l <= r)),
                        BiGe => Some(Constant::Bool(l >= r)),
                        BiGt => Some(Constant::Bool(l > r)),
                        _ => None,
                    }
                }
            },
            (Constant::F32(l), Some(Constant::F32(r))) => match op.node {
                BiAdd => Some(Constant::F32(l + r)),
                BiSub => Some(Constant::F32(l - r)),
                BiMul => Some(Constant::F32(l * r)),
                BiDiv => Some(Constant::F32(l / r)),
                BiRem => Some(Constant::F32(l * r)),
                BiEq => Some(Constant::Bool(l == r)),
                BiNe => Some(Constant::Bool(l != r)),
                BiLt => Some(Constant::Bool(l < r)),
                BiLe => Some(Constant::Bool(l <= r)),
                BiGe => Some(Constant::Bool(l >= r)),
                BiGt => Some(Constant::Bool(l > r)),
                _ => None,
            },
            (Constant::F64(l), Some(Constant::F64(r))) => match op.node {
                BiAdd => Some(Constant::F64(l + r)),
                BiSub => Some(Constant::F64(l - r)),
                BiMul => Some(Constant::F64(l * r)),
                BiDiv => Some(Constant::F64(l / r)),
                BiRem => Some(Constant::F64(l * r)),
                BiEq => Some(Constant::Bool(l == r)),
                BiNe => Some(Constant::Bool(l != r)),
                BiLt => Some(Constant::Bool(l < r)),
                BiLe => Some(Constant::Bool(l <= r)),
                BiGe => Some(Constant::Bool(l >= r)),
                BiGt => Some(Constant::Bool(l > r)),
                _ => None,
            },
            (l, r) => match (op.node, l, r) {
                (BiAnd, Constant::Bool(false), _) => Some(Constant::Bool(false)),
                (BiOr, Constant::Bool(true), _) => Some(Constant::Bool(true)),
                (BiAnd, Constant::Bool(true), Some(r)) | (BiOr, Constant::Bool(false), Some(r)) => Some(r),
                (BiBitXor, Constant::Bool(l), Some(Constant::Bool(r))) => Some(Constant::Bool(l ^ r)),
                (BiBitAnd, Constant::Bool(l), Some(Constant::Bool(r))) => Some(Constant::Bool(l & r)),
                (BiBitOr, Constant::Bool(l), Some(Constant::Bool(r))) => Some(Constant::Bool(l | r)),
                _ => None,
            },
        }
    }
}
