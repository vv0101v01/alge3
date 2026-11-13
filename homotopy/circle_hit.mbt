///|
// Circle HIT, integers Z, univalent winding cover (encode / decode),
// cancellation & pathToEquiv cells, Vogt adjointification, and ua_beta paths.

///|
using @face_bdd {dim_subst, face_subst}

///|
using @kernel {
  type DHitCellSpec,
  type DHitSpec,
  dim_is_one,
  dim_is_zero,
  force_value,
}

///|
/// Corner-turning path-inverse cancellation 3-cell:
/// for `alpha : Path space_ty r _`, gives `Path (Path space_ty r r) (alpha ⬝ sym(alpha)) (refl(r))`.
pub fn dpath_trans_sym_cancel_value(
  space_ty : DValue,
  alpha : DValue,
  r : DValue,
  dlevel : Int32,
) -> DValue {
  DVPathLam(t => {
    DVPathLam(i => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(i)), _ => r),
        tube_branch(face_simplify(FEq1(i)), k => {
          dapp_dim(alpha, dim_simplify(DAnd(DNeg(k), DNeg(t))))
        }),
        tube_branch(face_simplify(FEq1(t)), _ => r),
      ])
      hcomp_value(
        space_ty,
        branches,
        dapp_dim(alpha, dim_simplify(DAnd(i, DNeg(t)))),
        dlevel,
      )
    })
  })
}

///|
/// Canonical `pathToEquiv : Path U A B -> Equiv A B` along a type line.
pub fn path_to_equiv_value(
  line : (Dim) -> DValue,
  src : DValue,
  dst : DValue,
  level : Int32,
  dlevel : Int32,
) -> DValue {
  @kernel.path_to_equiv_value(line, src, dst, level, dlevel)
}

///|
/// Univalence β-path witnessing `coe (ua e) 0->1 x ≡ e.fwd x` in `dst`.
pub fn ua_beta_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  lvl : Int32,
  x : DValue,
  dlevel : Int32,
) -> DValue {
  @kernel.ua_beta_path_value(e, src, dst, lvl, x, dlevel)
}

///|
/// Vogt adjointification of an arbitrary quasi-inverse `(f, g, eps, eta)` into a
/// coherent half-adjoint section `eps'(y) := eps(f(g(y)))^{-1} ⬝ ap_f(eta(g(y))) ⬝ eps(y)`.
pub fn equiv_improved_sect_value(
  src : DValue,
  dst : DValue,
  f : DValue,
  g : DValue,
  sect_eps : DValue,
  retr_eta : DValue,
  dlevel : Int32,
) -> DValue {
  DValue::DVLam(y => {
    let gy = dapp_typed(g, y, dst)
    let fgy = dapp_typed(f, gy, src)
    let eps_fgy_inv = dpath_sym_value(dapp_typed(sect_eps, fgy, dst))
    let ap_eta_gy = dpath_cong_value(f, src, dapp_typed(retr_eta, gy, src))
    let eps_y = dapp_typed(sect_eps, y, dst)
    let left = dpath_trans_value(dst, eps_fgy_inv, ap_eta_gy, dlevel)
    dpath_trans_value(dst, left, eps_y, dlevel)
  })
}

// ---------------------------------------------------------------------------
// S^1 Higher Inductive Type, Loop Space, and Univalent Z Cover
// ---------------------------------------------------------------------------

///|
fn s1_circle_hit_spec() -> DHitSpec {
  DHitSpec::{
    name: "CircleHIT",
    num_params: 0,
    num_indices: 0,
    cells: [
      DHitCellSpec::{
        name: "base",
        arity: 0,
        dim_arity: 0,
        result_indices: [],
      },
      DHitCellSpec::{
        name: "loop",
        arity: 0,
        dim_arity: 1,
        result_indices: [],
      },
    ],
  }
}

///|
pub fn circle_hit_type_value() -> DValue {
  DValue::DVHitType(s1_circle_hit_spec(), [], [])
}

///|
pub fn circle_hit_base_value() -> DValue {
  DValue::DVHitCell(s1_circle_hit_spec(), 0, [], [], [])
}

///|
fn circle_hit_point(r : Dim) -> DValue {
  let s = dim_simplify(r)
  if dim_is_zero(s) || dim_is_one(s) {
    circle_hit_base_value()
  } else {
    DValue::DVHitCell(s1_circle_hit_spec(), 1, [], [], [s])
  }
}

///|
pub fn circle_hit_loop_path_value() -> DValue {
  DValue::DVPathLam(d => circle_hit_point(d))
}

///|
pub fn circle_loop_space_type_value() -> DValue {
  DValue::DVPathTy(
    _ => circle_hit_type_value(),
    circle_hit_base_value(),
    circle_hit_base_value(),
  )
}

///|
pub fn circle_hit_loop_power_value(k : Int32) -> DValue {
  let s1 = circle_hit_type_value()
  let base = circle_hit_base_value()
  let lp = circle_hit_loop_path_value()
  if k == 0 {
    dpath_refl_value(base)
  } else if k == 1 {
    lp
  } else if k == -1 {
    dpath_sym_value(lp)
  } else if k > 1 {
    let mut acc = lp
    for _i in 1..<k {
      acc = dpath_trans_value(s1, acc, lp, 0)
    }
    acc
  } else {
    let inv = dpath_sym_value(lp)
    let mut acc = inv
    for _i in 1..<-k {
      acc = dpath_trans_value(s1, acc, inv, 0)
    }
    acc
  }
}

///|
/// Canonical H-space self-loop `rot(x) : Path S^1 x x` on `S^1` (`rot(base) ≡ loop`).
pub fn circle_self_loop_value(x : DValue, dlevel : Int32) -> DValue {
  match force_value(x) {
    DVHitCell(s, 0, _, _, _) if s.name == "CircleHIT" =>
      circle_hit_loop_path_value()
    DVHitCell(s, 1, _, _, [r]) if s.name == "CircleHIT" => {
      let s1 = circle_hit_type_value()
      let sr = dim_simplify(r)
      if dim_is_zero(sr) || dim_is_one(sr) {
        circle_hit_loop_path_value()
      } else {
        DValue::DVPathLam(i => {
          let branches = dsystem_of([
            tube_branch(face_simplify(FEq0(i)), _ => x),
            tube_branch(face_simplify(FEq1(i)), _ => x),
            tube_branch(face_simplify(FEq0(sr)), _ => circle_hit_point(i)),
            tube_branch(face_simplify(FEq1(sr)), _ => circle_hit_point(i)),
          ])
          hcomp_value(s1, branches, x, dlevel)
        })
      }
    }
    DVCirclePoint(r) => {
      let sr = dim_simplify(r)
      if dim_is_zero(sr) || dim_is_one(sr) {
        DValue::DVPathLam(i => circle_point(i))
      } else {
        DValue::DVPathLam(i => {
          let branches = dsystem_of([
            tube_branch(face_simplify(FEq0(i)), _ => x),
            tube_branch(face_simplify(FEq1(i)), _ => x),
            tube_branch(face_simplify(FEq0(sr)), _ => circle_point(i)),
            tube_branch(face_simplify(FEq1(sr)), _ => circle_point(i)),
          ])
          hcomp_value(DVCircleTy, branches, x, dlevel)
        })
      }
    }
    _ => circle_hit_loop_path_value()
  }
}

///|
/// Signed integers `Z` represented in the dependent kernel as `Σ (is_nonneg : Bool), Nat`.
pub fn integer_type_value() -> DValue {
  DValue::DVSigma(DValue::DVBoolTy, _ => DValue::DVNatTy)
}

///|
pub fn integer_value(k : Int32) -> DValue {
  let nonneg = k >= 0
  let abs_k = if k < 0 { -k } else { k }
  let mut nat = DValue::DVZeroNat
  for _i in 0..<abs_k {
    nat = DValue::DVSucc(nat)
  }
  DValue::DVPair(DValue::DVBool(nonneg), nat)
}

///|
fn dim_winding_bit(r : Dim, var_id : Int32) -> Int32? {
  let r0 = dim_simplify(dim_subst(r, var_id, false))
  let r1 = dim_simplify(dim_subst(r, var_id, true))
  let b0 = if dim_is_zero(r0) {
    0
  } else if dim_is_one(r0) {
    1
  } else {
    return None
  }
  let b1 = if dim_is_zero(r1) {
    0
  } else if dim_is_one(r1) {
    1
  } else {
    return None
  }
  Some(b1 - b0)
}

///|
fn subst_dim_in_circle_val(
  path : (Dim) -> DValue,
  var_id : Int32,
  bit : Bool,
  k_id : Int32,
) -> DValue {
  fn subst_val(v : DValue) -> DValue {
    match force_value(v) {
      DVHitCell(s, 0, _, _, _) if s.name == "CircleHIT" =>
        circle_hit_base_value()
      DVHitCell(s, 1, _, _, [r]) if s.name == "CircleHIT" =>
        circle_hit_point(dim_subst(r, var_id, bit))
      DVCirclePoint(r) => circle_point(dim_subst(r, var_id, bit))
      DVNeutral(DNHComp(ty, sys, base)) => {
        let bs : Array[@kernel.DTubeBranch] = []
        for br in sys.branches {
          let bf = face_simplify(face_subst(br.face, var_id, bit))
          if !@face_bdd.face_is_bot_sem(bf) {
            bs.push(
              tube_branch(bf, k => {
                match k {
                  DVar(kv) if kv == k_id => subst_val((br.path)(k))
                  _ => subst_val((br.path)(k))
                }
              }),
            )
          }
        }
        DVNeutral(DNHComp(ty, dsystem_of(bs), subst_val(base)))
      }
      DVNeutral(DNComp(line, sys, base)) => {
        let bs : Array[@kernel.DTubeBranch] = []
        for br in sys.branches {
          let bf = face_simplify(face_subst(br.face, var_id, bit))
          if !@face_bdd.face_is_bot_sem(bf) {
            bs.push(tube_branch(bf, k => subst_val((br.path)(k))))
          }
        }
        DVNeutral(DNComp(line, dsystem_of(bs), subst_val(base)))
      }
      other => other
    }
  }
  subst_val(path(Dim::DVar(k_id)))
}

///|
fn s1_val_winding_wrt(v0 : DValue, var_id : Int32) -> Int32? {
  match force_value(v0) {
    DVHitCell(s, 0, _, _, _) if s.name == "CircleHIT" => Some(0)
    DVHitCell(s, 1, _, _, [r]) if s.name == "CircleHIT" =>
      dim_winding_bit(r, var_id)
    DVCirclePoint(r) => dim_winding_bit(r, var_id)
    DVNeutral(DNComp(_, sys, base)) | DVNeutral(DNHComp(_, sys, base)) => {
      let w_base = match s1_val_winding_wrt(base, var_id) {
        Some(w) => w
        None => return None
      }
      let mut w_at_0 = 0
      let mut w_at_1 = 0
      let k_id = var_id + 97
      for br in sys.branches {
        let f0 = face_simplify(face_subst(br.face, var_id, false))
        let f1 = face_simplify(face_subst(br.face, var_id, true))
        if f0 == FTop {
          match
            s1_val_winding_wrt(
              subst_dim_in_circle_val(br.path, var_id, false, k_id),
              k_id,
            ) {
            Some(dw) => w_at_0 = dw
            None => return None
          }
        }
        if f1 == FTop {
          match
            s1_val_winding_wrt(
              subst_dim_in_circle_val(br.path, var_id, true, k_id),
              k_id,
            ) {
            Some(dw) => w_at_1 = dw
            None => return None
          }
        }
      }
      Some(w_base + w_at_1 - w_at_0)
    }
    _ => None
  }
}

///|
pub fn circle_encode_value(path_val : DValue, dlevel : Int32) -> DValue {
  let d = Dim::DVar(dlevel)
  match s1_val_winding_wrt(dapp_dim(path_val, d), dlevel) {
    Some(w) => integer_value(w)
    None => integer_value(0)
  }
}

///|
/// Contracting retraction path `Path (Ω S^1) (decode(encode(p))) p` in the
/// loop space of `S^1`, normalizing `0`-endpoint to the canonical loop power.
pub fn circle_decode_encode_retr_value(
  path_val : DValue,
  dlevel : Int32,
) -> DValue {
  let w = match
    s1_val_winding_wrt(dapp_dim(path_val, Dim::DVar(dlevel)), dlevel) {
    Some(k) => k
    None => 0
  }
  let canon = circle_hit_loop_power_value(w)
  let s1 = circle_hit_type_value()
  let base = circle_hit_base_value()
  DValue::DVPathLam(t => {
    DValue::DVPathLam(i => {
      let branches = dsystem_of([
        tube_branch(face_simplify(FEq0(t)), _ => dapp_dim(canon, i)),
        tube_branch(face_simplify(FEq1(t)), _ => dapp_dim(path_val, i)),
        tube_branch(face_simplify(FEq0(i)), _ => base),
        tube_branch(face_simplify(FEq1(i)), _ => base),
      ])
      hcomp_value(s1, branches, base, dlevel)
    })
  })
}
