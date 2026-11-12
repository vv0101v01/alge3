///|
// First-class equivalences, equivalence-presented Glue types, univalence (`ua`),
// and their evaluation, type inference, conversion, quoting, and Kan composition.

///|
pub struct DEquivParts {
  src : DValue
  dst : DValue
  fwd : DValue
  bwd : DValue
  sect : DValue
  retr : DValue
}

///|
pub fn equiv_sect_type(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
) -> DValue {
  DVPi(dst, y => {
    DVPathTy(_ => dst, dapp_typed(fwd, dapp_typed(bwd, y, dst), src), y)
  })
}

///|
pub fn equiv_retr_type(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
) -> DValue {
  DVPi(src, x => {
    DVPathTy(_ => src, dapp_typed(bwd, dapp_typed(fwd, x, src), dst), x)
  })
}

///|
pub fn equiv_types_of_value(v : DValue) -> (DValue, DValue) {
  match force_value(v) {
    DVEquiv(src, dst, _, _, _, _) => (src, dst)
    DVNeutral(DNEquivAnn(_, src, dst)) => (src, dst)
    _ => (DVUnitTy, DVUnitTy)
  }
}

///|
pub fn equiv_parts(v : DValue, src : DValue, dst : DValue) -> DEquivParts {
  match force_value(v) {
    DVEquiv(s, d, fwd, bwd, sect, retr) =>
      DEquivParts::{ src: s, dst: d, fwd, bwd, sect, retr, }
    DVNeutral(n) => {
      let inner = match n {
        DNEquivAnn(x, _, _) => x
        _ => n
      }
      let fwd = reflect_neutral_at_type(
        DNEquivFwd(inner, src, dst),
        DVPi(src, _ => dst),
      )
      let bwd = reflect_neutral_at_type(
        DNEquivBwd(inner, src, dst),
        DVPi(dst, _ => src),
      )
      let sect = reflect_neutral_at_type(
        DNEquivSect(inner, src, dst),
        equiv_sect_type(src, dst, fwd, bwd),
      )
      let retr = reflect_neutral_at_type(
        DNEquivRetr(inner, src, dst),
        equiv_retr_type(src, dst, fwd, bwd),
      )
      DEquivParts::{ src, dst, fwd, bwd, sect, retr, }
    }
    _ => {
      let id = DVLam(x => x)
      let refl = DVLam(x => DVPathLam(_ => x))
      DEquivParts::{ src, dst, fwd: id, bwd: id, sect: refl, retr: refl, }
    }
  }
}

///|
pub fn equiv_fwd_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  equiv_parts(e, src, dst).fwd
}

///|
pub fn equiv_bwd_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  equiv_parts(e, src, dst).bwd
}

///|
pub fn equiv_sect_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  equiv_parts(e, src, dst).sect
}

///|
pub fn equiv_retr_value(e : DValue, src : DValue, dst : DValue) -> DValue {
  equiv_parts(e, src, dst).retr
}

///|
pub fn equiv_fun_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  x : DValue,
) -> DValue {
  dapp_typed(equiv_fwd_value(e, src, dst), x, src)
}

///|
pub fn equiv_inv_fun_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  y : DValue,
) -> DValue {
  dapp_typed(equiv_bwd_value(e, src, dst), y, dst)
}

///|
pub fn equiv_make_value(
  src : DValue,
  dst : DValue,
  fwd : DValue,
  bwd : DValue,
  sect : DValue,
  retr : DValue,
) -> DValue {
  DVEquiv(src, dst, fwd, bwd, sect, retr)
}

///|
pub fn equiv_id_value(a : DValue) -> DValue {
  let id = DVLam(x => x)
  let refl = DVLam(x => DVPathLam(_ => x))
  DVEquiv(a, a, id, id, refl, refl)
}

///|
pub fn eval_mk_equiv_term(
  a : DTerm,
  b : DTerm,
  f : DTerm,
  g : DTerm,
  sect : DTerm,
  retr : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  DVEquiv(
    deval_dim(a, env, denv),
    deval_dim(b, env, denv),
    deval_dim(f, env, denv),
    deval_dim(g, env, denv),
    deval_dim(sect, env, denv),
    deval_dim(retr, env, denv),
  )
}

///|
pub fn bool_not_equiv_term() -> DTerm {
  let not_body = DBoolElim(DBoolTy, DBoolLit(false), DBoolLit(true), DTVar(0))
  let not_fn = DLam(DBoolTy, not_body)
  let refl_fn = DLam(
    DBoolTy,
    DBoolElim(
      DPathP(DBoolTy, DApp(not_fn, DApp(not_fn, DTVar(0))), DTVar(0)),
      DLamDim(DBoolLit(true)),
      DLamDim(DBoolLit(false)),
      DTVar(0),
    ),
  )
  DMkEquiv(DBoolTy, DBoolTy, not_fn, not_fn, refl_fn, refl_fn)
}

///|
pub fn infer_equiv_ty(
  a : DTerm,
  b : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match (d_as_type(a, ctx, env, denv), d_as_type(b, ctx, env, denv)) {
    (Some(at), Some(bt)) => {
      let lvl = if at.level > bt.level { at.level } else { bt.level }
      Some(DInfer::{
        value: DVEquivTy(at.value, bt.value, lvl),
        ty: DVUniv(lvl),
      })
    }
    _ => None
  }
}

///|
pub fn infer_mk_equiv(
  a : DTerm,
  b : DTerm,
  f : DTerm,
  g : DTerm,
  sect : DTerm,
  retr : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match (d_as_type(a, ctx, env, denv), d_as_type(b, ctx, env, denv)) {
    (Some(at), Some(bt)) => {
      let src = at.value
      let dst = bt.value
      let fwd_ty = DVPi(src, _ => dst)
      let bwd_ty = DVPi(dst, _ => src)
      match
        (d_check(f, fwd_ty, ctx, env, denv), d_check(g, bwd_ty, ctx, env, denv)) {
        (Some(fv), Some(gv)) =>
          match
            (
              d_check(sect, equiv_sect_type(src, dst, fv, gv), ctx, env, denv),
              d_check(retr, equiv_retr_type(src, dst, fv, gv), ctx, env, denv),
            ) {
            (Some(sv), Some(rv)) => {
              let lvl = if at.level > bt.level { at.level } else { bt.level }
              Some(DInfer::{
                value: DVEquiv(src, dst, fv, gv, sv, rv),
                ty: DVEquivTy(src, dst, lvl),
              })
            }
            _ => None
          }
        _ => None
      }
    }
    _ => None
  }
}

///|
pub fn infer_equiv_projection(
  which : Int32,
  e : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match d_infer(e, ctx, env, denv) {
    Some(inf) =>
      match force_value(inf.ty) {
        DVEquivTy(src, dst, _) => {
          let p = equiv_parts(inf.value, src, dst)
          if which == 0 {
            Some(DInfer::{ value: p.fwd, ty: DVPi(src, _ => dst), })
          } else if which == 1 {
            Some(DInfer::{ value: p.bwd, ty: DVPi(dst, _ => src), })
          } else if which == 2 {
            Some(DInfer::{
              value: p.sect,
              ty: equiv_sect_type(src, dst, p.fwd, p.bwd),
            })
          } else {
            Some(DInfer::{
              value: p.retr,
              ty: equiv_retr_type(src, dst, p.fwd, p.bwd),
            })
          }
        }
        _ => None
      }
    None => None
  }
}

///|
pub fn comp_equiv_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let eq_at = (d : Dim) => {
    match force_value(line(d)) {
      DVEquivTy(s, t, _) => (s, t)
      _ => (DVUnitTy, DVUnitTy)
    }
  }
  let (s0, t0) = eq_at(DZero)
  let src_line = (j : Dim) => eq_at(j).0
  let dst_line = (j : Dim) => eq_at(j).1
  let p_base = equiv_parts(base, s0, t0)
  let fwd_line = (j : Dim) => DVPi(src_line(j), _ => dst_line(j))
  let bwd_line = (j : Dim) => DVPi(dst_line(j), _ => src_line(j))
  let fwd_branches = dsystem_map(branches, p => {
    j => {
      let (sj, tj) = eq_at(j)
      equiv_fwd_value(p(j), sj, tj)
    }
  })
  let bwd_branches = dsystem_map(branches, p => {
    j => {
      let (sj, tj) = eq_at(j)
      equiv_bwd_value(p(j), sj, tj)
    }
  })
  let fwd_fill = fill_value(fwd_line, fwd_branches, p_base.fwd, dlevel)
  let bwd_fill = fill_value(bwd_line, bwd_branches, p_base.bwd, dlevel)
  let fwd1 = fwd_fill(DOne)
  let bwd1 = bwd_fill(DOne)
  let (s1, t1) = eq_at(DOne)
  let sect_branches = dsystem_map(branches, p => {
    j => {
      let (sj, tj) = eq_at(j)
      equiv_sect_value(p(j), sj, tj)
    }
  })
  let retr_branches = dsystem_map(branches, p => {
    j => {
      let (sj, tj) = eq_at(j)
      equiv_retr_value(p(j), sj, tj)
    }
  })
  let sect1 = comp_value(
    j => equiv_sect_type(src_line(j), dst_line(j), fwd_fill(j), bwd_fill(j)),
    sect_branches,
    p_base.sect,
    dlevel,
  )
  let retr1 = comp_value(
    j => equiv_retr_type(src_line(j), dst_line(j), fwd_fill(j), bwd_fill(j)),
    retr_branches,
    p_base.retr,
    dlevel,
  )
  let _ = (s1, t1)
  DVEquiv(s1, t1, fwd1, bwd1, sect1, retr1)
}

// ---------------------------------------------------------------------------
// Equivalence-presented Glue & Univalence (`ua`)
// ---------------------------------------------------------------------------

///|
pub fn glue_equiv_domain_face(branches : Array[DEquivBranchValue]) -> Face {
  let mut f = Face::FBot
  for br in branches {
    let bf = face_simplify(br.face)
    if !face_is_bot_sem(bf) {
      f = face_simplify(FOr(f, bf))
    }
  }
  f
}

///|
pub fn as_glue_equiv(v : DValue) -> DGlueEquivParts? {
  match force_value(v) {
    DVGlueEquiv(branches, base, level) => {
      let kept : Array[DEquivBranchValue] = []
      for br in branches {
        let bf = face_simplify(br.face)
        if !face_is_bot_sem(bf) {
          kept.push(dequiv_branch_value(bf, br.ty, br.equiv))
        }
      }
      Some(DGlueEquivParts::{
        branches: kept,
        face: glue_equiv_domain_face(kept),
        base,
        level,
      })
    }
    _ => None
  }
}

///|
pub fn glue_equiv_top_index(parts : DGlueEquivParts) -> Int32 {
  for i in 0..<parts.branches.length() {
    if face_is_top_sem(parts.branches[i].face) {
      return i
    }
  }
  -1
}

///|
pub fn glue_equiv_collapse(v : DValue) -> DValue {
  match as_glue_equiv(v) {
    Some(parts) => {
      let top = glue_equiv_top_index(parts)
      if top >= 0 {
        parts.branches[top].ty
      } else if face_is_bot_sem(parts.face) {
        parts.base
      } else {
        v
      }
    }
    None => force_value(v)
  }
}

///|
pub fn glue_equiv_partial_values(
  parts : DGlueEquivParts,
  v : DValue,
) -> Array[DValue] {
  let n = parts.branches.length()
  if n == 0 {
    return []
  }
  let top = glue_equiv_top_index(parts)
  if top >= 0 {
    let out : Array[DValue] = []
    for i in 0..<n {
      if i == top {
        out.push(v)
      } else {
        out.push(
          equiv_inv_fun_value(
            parts.branches[i].equiv,
            parts.branches[i].ty,
            parts.base,
            equiv_fun_value(
              parts.branches[top].equiv,
              parts.branches[top].ty,
              parts.base,
              v,
            ),
          ),
        )
      }
    }
    return out
  }
  if face_is_bot_sem(parts.face) {
    return []
  }
  let out : Array[DValue] = []
  match force_value(v) {
    DVPair(stored, _) =>
      match force_value(stored) {
        DVPartial(p) =>
          for i in 0..<n {
            let wanted = parts.branches[i].face
            let mut found = DVUnit
            let mut ok = false
            for k in 0..<p.branches.length() {
              if same_face_sem(wanted, p.branches[k].face) {
                found = p.branches[k].value
                ok = true
                break
              }
            }
            if !ok && i < p.branches.length() {
              found = p.branches[i].value
            }
            out.push(found)
          }
        raw =>
          for _i in 0..<n {
            out.push(raw)
          }
      }
    DVNeutral(neu) =>
      for i in 0..<n {
        out.push(
          reflect_neutral_at_type(
            DNFst(neu, _ => parts.base),
            parts.branches[i].ty,
          ),
        )
      }
    raw =>
      for _i in 0..<n {
        out.push(raw)
      }
  }
  out
}

///|
pub fn glue_equiv_base_of(parts : DGlueEquivParts, v : DValue) -> DValue {
  let top = glue_equiv_top_index(parts)
  if top >= 0 {
    let br = parts.branches[top]
    return equiv_fun_value(br.equiv, br.ty, parts.base, v)
  }
  if face_is_bot_sem(parts.face) {
    return v
  }
  match force_value(v) {
    DVPair(_, b) => b
    DVNeutral(n) => DVNeutral(DNUnglueEquiv(n, parts))
    other => other
  }
}

///|
pub fn glue_equiv_store_partial(
  parts : DGlueEquivParts,
  values : Array[DValue],
) -> DValue {
  if values.length() == 0 {
    DVUnit
  } else if parts.branches.length() <= 1 {
    values[0]
  } else {
    let bs : Array[DFaceValue] = []
    for i in 0..<parts.branches.length() {
      let val = if i < values.length() { values[i] } else { DVUnit }
      bs.push(dface_value(parts.branches[i].face, val))
    }
    DVPartial(partial_of(bs))
  }
}

///|
pub fn glue_equiv_restrict_arg_under_face(
  bface : Face,
  dom_j : DValue,
  arg : DValue,
) -> DValue {
  match as_glue_equiv(dom_j) {
    Some(parts) =>
      if parts.branches.length() == 0 {
        arg
      } else {
        for i in 0..<parts.branches.length() {
          let br = parts.branches[i]
          let nvars = face_nvars_sem(FOr(bface, br.face))
          if face_eq_mod(FAnd(bface, br.face), bface, nvars) {
            let ps = glue_equiv_partial_values(parts, arg)
            if i < ps.length() {
              return ps[i]
            }
          }
        }
        arg
      }
    None => arg
  }
}

///|
pub fn eval_glue_equiv_term(
  base : DTerm,
  branches : Array[DEquivBranch],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let bv = deval_dim(base, env, denv)
  let evaled : Array[DEquivBranchValue] = []
  for br in branches {
    let f = face_eval_env(br.face, denv)
    if !face_is_bot_sem(f) {
      evaled.push(
        dequiv_branch_value(
          f,
          deval_dim(br.ty, env, denv),
          deval_dim(br.equiv, env, denv),
        ),
      )
    }
  }
  DVGlueEquiv(evaled, bv, 0)
}

///|
pub fn eval_unglue_equiv_term(
  term : DTerm,
  base : DTerm,
  branches : Array[DEquivBranch],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let tv = deval_dim(term, env, denv)
  match eval_glue_equiv_term(base, branches, env, denv) {
    DVGlueEquiv(bs, bv, lvl) => {
      let parts = DGlueEquivParts::{
        branches: bs,
        face: glue_equiv_domain_face(bs),
        base: bv,
        level: lvl,
      }
      glue_equiv_base_of(parts, tv)
    }
    _ => tv
  }
}

///|
pub fn ua_type_at(
  e : DValue,
  src : DValue,
  dst : DValue,
  lvl : Int32,
  d : Dim,
) -> DValue {
  let f0 = face_simplify(FEq0(d))
  let f1 = face_simplify(FEq1(d))
  if face_is_top_sem(f0) {
    src
  } else if face_is_top_sem(f1) {
    dst
  } else {
    DVGlueEquiv(
      [
        dequiv_branch_value(f0, src, e),
        dequiv_branch_value(f1, dst, equiv_id_value(dst)),
      ],
      dst,
      lvl,
    )
  }
}

///|
pub fn ua_line_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  lvl : Int32,
) -> (Dim) -> DValue {
  d => ua_type_at(e, src, dst, lvl, d)
}

///|
pub fn ua_value(e : DValue, src : DValue, dst : DValue, lvl : Int32) -> DValue {
  DVPathLam(d => ua_type_at(e, src, dst, lvl, d))
}

///|
pub fn path_to_equiv_value(
  line : (Dim) -> DValue,
  src : DValue,
  dst : DValue,
  _level : Int32,
  dlevel : Int32,
) -> DValue {
  let fwd = DValue::DVLam(x => coe_value(line, DZero, DOne, x, dlevel))
  let bwd = DValue::DVLam(y => coe_value(line, DOne, DZero, y, dlevel))
  let sect = DValue::DVLam(y => {
    DValue::DVPathLam(s => {
      coe_value(line, s, DOne, coe_value(line, DOne, s, y, dlevel), dlevel)
    })
  })
  let retr = DValue::DVLam(x => {
    DValue::DVPathLam(s => {
      coe_value(
        line,
        DNeg(s),
        DZero,
        coe_value(line, DZero, DNeg(s), x, dlevel),
        dlevel,
      )
    })
  })
  equiv_make_value(src, dst, fwd, bwd, sect, retr)
}

///|
fn path_trans_kernel(
  space_ty : DValue,
  p : DValue,
  q : DValue,
  dlevel : Int32,
) -> DValue {
  let x0 = dapp_dim(p, DZero)
  DVPathLam(i => {
    let branches = dsystem_of([
      tube_branch(face_simplify(FEq0(i)), _ => x0),
      tube_branch(face_simplify(FEq1(i)), j => dapp_dim(q, j)),
    ])
    hcomp_value(space_ty, branches, dapp_dim(p, i), dlevel + 1)
  })
}

///|
/// Univalence β-path witnessing `coe (ua e) 0->1 x ≡ e.fwd x` in `dst`.
pub fn ua_beta_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  _lvl : Int32,
  x : DValue,
  dlevel : Int32,
) -> DValue {
  let fx = equiv_fun_value(e, src, dst, x)
  DValue::DVPathLam(i => coe_value(_ => dst, i, DOne, fx, dlevel))
}

///|
/// Univalence backward β-path witnessing `coe (ua e) 1->0 y ≡ e.bwd y` in `src`.
pub fn ua_beta_inv_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  _lvl : Int32,
  y : DValue,
  dlevel : Int32,
) -> DValue {
  DValue::DVPathLam(i => {
    equiv_inv_fun_value(e, src, dst, coe_value(_ => dst, i, DOne, y, dlevel))
  })
}

///|
/// Univalence identity coherence: `Path (Path U A A) (ua (idEquiv A)) (refl A)`.
pub fn ua_id_path_value(a_ty : DValue, lvl : Int32, _dlevel : Int32) -> DValue {
  let id_e = equiv_id_value(a_ty)
  DVPathLam(t => {
    DVPathLam(i => {
      let f0 = face_simplify(FOr(FEq0(i), FEq1(t)))
      let f1 = face_simplify(FEq1(i))
      if face_is_top_sem(f0) || face_is_top_sem(f1) {
        a_ty
      } else {
        DVGlueEquiv(
          [
            dequiv_branch_value(f0, a_ty, id_e),
            dequiv_branch_value(f1, a_ty, id_e),
          ],
          a_ty,
          lvl,
        )
      }
    })
  })
}

///|
fn equiv_coe_tail_value(dst : DValue, t : Dim, dlevel : Int32) -> DValue {
  let nt = dim_simplify(DNeg(t))
  let fwd = DVLam(y => coe_value(_ => dst, nt, DOne, y, dlevel))
  let bwd = DVLam(y => coe_value(_ => dst, DOne, nt, y, dlevel))
  let sect = DVLam(y => {
    DVPathLam(s => {
      coe_value(
        _ => dst,
        dim_simplify(DOr(nt, s)),
        DOne,
        coe_value(_ => dst, DOne, dim_simplify(DOr(nt, s)), y, dlevel),
        dlevel,
      )
    })
  })
  let retr = DVLam(y => {
    DVPathLam(s => {
      coe_value(
        _ => dst,
        dim_simplify(DOr(nt, s)),
        DOne,
        coe_value(_ => dst, dim_simplify(DOr(nt, s)), DOne, y, dlevel),
        dlevel,
      )
    })
  })
  equiv_make_value(dst, dst, fwd, bwd, sect, retr)
}

///|
/// Univalence η-path (`ua ∘ pathToEquiv ~ id`):
/// `Path (Path U src dst) (ua (pathToEquiv line)) (DVPathLam line)`.
pub fn ua_eta_path_value(
  line : (Dim) -> DValue,
  src : DValue,
  dst : DValue,
  lvl : Int32,
  dlevel : Int32,
) -> DValue {
  let p_eq = path_to_equiv_value(line, src, dst, lvl, dlevel)
  let refl_dst_eq = path_to_equiv_value(_ => dst, dst, dst, lvl, dlevel)
  let sq_cchm : DValue = DVPathLam(t => {
    DVPathLam(i => {
      let ft = face_simplify(FEq1(t))
      let f0 = face_simplify(FEq0(i))
      let f1 = face_simplify(FEq1(i))
      if face_is_top_sem(ft) {
        line(i)
      } else if face_is_top_sem(f0) {
        src
      } else if face_is_top_sem(f1) {
        dst
      } else {
        let tail_eq = path_to_equiv_value(
          s => line(dim_simplify(DOr(i, s))),
          line(i),
          dst,
          lvl,
          dlevel + 2,
        )
        DVGlueEquiv(
          [
            dequiv_branch_value(f0, src, p_eq),
            dequiv_branch_value(f1, dst, refl_dst_eq),
            dequiv_branch_value(ft, line(i), tail_eq),
          ],
          dst,
          lvl,
        )
      }
    })
  })
  if conv_at(
      0,
      dlevel + 2,
      DVEquivTy(dst, dst, lvl),
      refl_dst_eq,
      equiv_id_value(dst),
    ) {
    sq_cchm
  } else {
    let sq_bridge : DValue = DVPathLam(t => {
      DVPathLam(i => {
        let f0 = face_simplify(FEq0(i))
        let f1 = face_simplify(FEq1(i))
        if face_is_top_sem(f0) {
          src
        } else if face_is_top_sem(f1) {
          dst
        } else {
          DVGlueEquiv(
            [
              dequiv_branch_value(f0, src, p_eq),
              dequiv_branch_value(
                f1,
                dst,
                equiv_coe_tail_value(dst, t, dlevel + 2),
              ),
            ],
            dst,
            lvl,
          )
        }
      })
    })
    DVPathLam(t => {
      DVPathLam(i => {
        let branches = dsystem_of([
          tube_branch(face_simplify(FEq0(t)), _ => {
            dapp_dim(dapp_dim(sq_bridge, DZero), i)
          }),
          tube_branch(face_simplify(FEq1(t)), j => {
            dapp_dim(dapp_dim(sq_cchm, j), i)
          }),
          tube_branch(face_simplify(FEq0(i)), _ => src),
          tube_branch(face_simplify(FEq1(i)), _ => dst),
        ])
        hcomp_value(
          DVUniv(lvl),
          branches,
          dapp_dim(dapp_dim(sq_bridge, t), i),
          dlevel + 2,
        )
      })
    })
  }
}

///|
/// Univalence retraction path (`pathToEquiv ∘ ua ~ id`):
/// `Path (Equiv src dst) (pathToEquiv (ua e)) e`.
pub fn path_to_equiv_ua_beta_path_value(
  e : DValue,
  src : DValue,
  dst : DValue,
  _lvl : Int32,
  dlevel : Int32,
) -> DValue {
  let ep = equiv_parts(e, src, dst)
  DVPathLam(t => {
    let fwd_t = DVLam(x => {
      coe_value(_ => dst, t, DOne, dapp_typed(ep.fwd, x, src), dlevel)
    })
    let bwd_t = DVLam(y => {
      dapp_typed(ep.bwd, coe_value(_ => dst, t, DOne, y, dlevel), dst)
    })
    let sect_t = DVLam(y => {
      let cy = coe_value(_ => dst, t, DOne, y, dlevel)
      let sect_cy = dapp_typed(ep.sect, cy, dst)
      let h1 : DValue = DVPathLam(s => {
        coe_value(_ => dst, t, DOne, dapp_dim(sect_cy, s), dlevel)
      })
      let h2 : DValue = DVPathLam(s => {
        let ts = dim_simplify(DOr(t, s))
        coe_value(
          _ => dst,
          ts,
          DOne,
          coe_value(_ => dst, ts, DOne, y, dlevel),
          dlevel,
        )
      })
      path_trans_kernel(dst, h1, h2, dlevel + 1)
    })
    let retr_t = DVLam(x => {
      let fx = dapp_typed(ep.fwd, x, src)
      let k1 : DValue = DVPathLam(s => {
        let ts = dim_simplify(DOr(t, s))
        dapp_typed(
          ep.bwd,
          coe_value(
            _ => dst,
            ts,
            DOne,
            coe_value(_ => dst, ts, DOne, fx, dlevel),
            dlevel,
          ),
          dst,
        )
      })
      let k2 = dapp_typed(ep.retr, x, src)
      path_trans_kernel(src, k1, k2, dlevel + 1)
    })
    equiv_make_value(src, dst, fwd_t, bwd_t, sect_t, retr_t)
  })
}

///|
/// First-class Voevodsky Univalence equivalence:
/// `Equiv (Equiv src dst) (Path U src dst)`.
pub fn univalence_equiv_value(
  src : DValue,
  dst : DValue,
  lvl : Int32,
  dlevel : Int32,
) -> DValue {
  let eq_ty = DVEquivTy(src, dst, lvl)
  let path_ty = DVPathTy(_ => DVUniv(lvl), src, dst)
  let fwd = DVLam(e => ua_value(e, src, dst, lvl))
  let bwd = DVLam(p => {
    path_to_equiv_value(d => dapp_dim(p, d), src, dst, lvl, dlevel)
  })
  let sect = DVLam(p => {
    ua_eta_path_value(d => dapp_dim(p, d), src, dst, lvl, dlevel)
  })
  let retr = DVLam(e => {
    path_to_equiv_ua_beta_path_value(e, src, dst, lvl, dlevel)
  })
  equiv_make_value(eq_ty, path_ty, fwd, bwd, sect, retr)
}

///|
pub fn eval_ua_term(e : DTerm, env : DEnv, denv : DDimEnv) -> DValue {
  let ev = deval_dim(e, env, denv)
  let (src, dst) = equiv_types_of_value(ev)
  ua_value(ev, src, dst, 0)
}

///|
pub fn eval_path_to_equiv_term(p : DTerm, env : DEnv, denv : DDimEnv) -> DValue {
  let pv = deval_dim(p, env, denv)
  let line = (d : Dim) => dapp_dim(pv, d)
  path_to_equiv_value(line, line(DZero), line(DOne), 0, ddim_len(denv))
}

///|
pub fn infer_glue_equiv(
  base : DTerm,
  branches : Array[DEquivBranch],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match d_as_type(base, ctx, env, denv) {
    Some(bt) => {
      let mut max_lvl = bt.level
      let evaled : Array[DEquivBranchValue] = []
      for br in branches {
        let f = face_eval_env(br.face, denv)
        match d_as_type(br.ty, ctx, env, denv) {
          Some(tt) => {
            if tt.level > max_lvl {
              max_lvl = tt.level
            }
            match
              d_check(
                br.equiv,
                DVEquivTy(tt.value, bt.value, max_lvl),
                ctx,
                env,
                denv,
              ) {
              Some(ev) =>
                if !face_is_bot_sem(f) {
                  evaled.push(dequiv_branch_value(f, tt.value, ev))
                }
              None => return None
            }
          }
          None => return None
        }
      }
      Some(DInfer::{
        value: DVGlueEquiv(evaled, bt.value, max_lvl),
        ty: DVUniv(max_lvl),
      })
    }
    None => None
  }
}

///|
pub fn infer_unglue_equiv(
  term : DTerm,
  base : DTerm,
  branches : Array[DEquivBranch],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match infer_glue_equiv(base, branches, ctx, env, denv) {
    Some(ginf) =>
      match d_check(term, ginf.value, ctx, env, denv) {
        Some(tv) =>
          match as_glue_equiv(ginf.value) {
            Some(parts) =>
              Some(DInfer::{
                value: glue_equiv_base_of(parts, tv),
                ty: parts.base,
              })
            None => Some(DInfer::{ value: tv, ty: deval_dim(base, env, denv), })
          }
        None => None
      }
    None => None
  }
}

///|
pub fn infer_ua(e : DTerm, ctx : DEnv, env : DEnv, denv : DDimEnv) -> DInfer? {
  match d_infer(e, ctx, env, denv) {
    Some(inf) =>
      match force_value(inf.ty) {
        DVEquivTy(src, dst, lvl) =>
          Some(DInfer::{
            value: ua_value(inf.value, src, dst, lvl),
            ty: DVPathTy(_ => DVUniv(lvl), src, dst),
          })
        _ => None
      }
    None => None
  }
}

///|
pub fn infer_path_to_equiv(
  p : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  match d_infer(p, ctx, env, denv) {
    Some(inf) =>
      match as_path(inf.ty) {
        Some(parts) =>
          match as_univ_level((parts.line)(DVar(ddim_len(denv)))) {
            Some(lvl) =>
              Some(DInfer::{
                value: path_to_equiv_value(
                  d => dapp_dim(inf.value, d),
                  parts.left,
                  parts.right,
                  lvl,
                  ddim_len(denv),
                ),
                ty: DVEquivTy(parts.left, parts.right, lvl),
              })
            None => None
          }
        None => None
      }
    None => None
  }
}

///|
pub fn d_check_glue_equiv_partial(
  a : DTerm,
  g : DGlueEquivParts,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> Array[DValue]? {
  let values : Array[DValue] = []
  match a {
    DPartial(supplied) =>
      for i in 0..<g.branches.length() {
        let br = g.branches[i]
        let mut body = DUnitLit
        let mut found = false
        for k in 0..<supplied.length() {
          if same_face_sem(br.face, face_eval_env(supplied[k].face, denv)) {
            body = supplied[k].body
            found = true
            break
          }
        }
        if !found {
          return None
        }
        match d_check(body, br.ty, ctx, env, denv) {
          Some(v) => values.push(v)
          None => return None
        }
      }
    _ =>
      for br in g.branches {
        match d_check(a, br.ty, ctx, env, denv) {
          Some(v) => values.push(v)
          None => return None
        }
      }
  }
  Some(values)
}

///|
pub fn glue_equiv_systems_conv(
  level : Int32,
  dlevel : Int32,
  base : DValue,
  a : Array[DEquivBranchValue],
  b : Array[DEquivBranchValue],
) -> Bool {
  let ka : Array[DEquivBranchValue] = []
  for br in a {
    if !face_is_bot_sem(br.face) {
      ka.push(br)
    }
  }
  let kb : Array[DEquivBranchValue] = []
  for br in b {
    if !face_is_bot_sem(br.face) {
      kb.push(br)
    }
  }
  if ka.length() != kb.length() {
    return false
  }
  for i in 0..<ka.length() {
    if !same_face_sem(ka[i].face, kb[i].face) ||
      !conv_ty(level, dlevel, ka[i].ty, kb[i].ty) ||
      !conv_at(
        level,
        dlevel,
        DVEquivTy(ka[i].ty, base, 0),
        ka[i].equiv,
        kb[i].equiv,
      ) {
      return false
    }
  }
  true
}

///|
pub fn quote_glue_equiv_type(
  level : Int32,
  dlevel : Int32,
  parts : DGlueEquivParts,
) -> DTerm {
  let bs : Array[DEquivBranch] = []
  for br in parts.branches {
    bs.push(
      d_equiv_branch(
        face_quote(br.face, dlevel),
        quote_ty(level, dlevel, br.ty),
        quote_at(
          level,
          dlevel,
          DVEquivTy(br.ty, parts.base, parts.level),
          br.equiv,
        ),
      ),
    )
  }
  DGlueEquiv(quote_ty(level, dlevel, parts.base), bs)
}

///|
pub fn quote_unglue_equiv_neutral(
  level : Int32,
  dlevel : Int32,
  inner : DNeutral,
  parts : DGlueEquivParts,
) -> DTerm {
  let gty = DVGlueEquiv(parts.branches, parts.base, parts.level)
  let bs : Array[DEquivBranch] = []
  for br in parts.branches {
    bs.push(
      d_equiv_branch(
        face_quote(br.face, dlevel),
        quote_ty(level, dlevel, br.ty),
        quote_at(
          level,
          dlevel,
          DVEquivTy(br.ty, parts.base, parts.level),
          br.equiv,
        ),
      ),
    )
  }
  DUnglueEquiv(
    quote_dneutral(level, dlevel, inner, gty),
    quote_ty(level, dlevel, parts.base),
    bs,
  )
}

///|
fn glue_equiv_parts_at(line : (Dim) -> DValue, d : Dim) -> DGlueEquivParts {
  let ty = line(d)
  match as_glue_equiv(ty) {
    Some(parts) => parts
    None => DGlueEquivParts::{ branches: [], face: FBot, base: ty, level: 0, }
  }
}

///|
fn glue_equiv_endpoint_parts(
  line : (Dim) -> DValue,
  d : Dim,
  dlevel : Int32,
) -> DGlueEquivParts {
  let parts = glue_equiv_parts_at(line, d)
  if parts.branches.length() > 0 {
    return parts
  }
  let generic = glue_equiv_parts_at(line, DVar(dlevel))
  if generic.branches.length() == 0 {
    return parts
  }
  let ds = dim_simplify(d)
  if dim_is_zero(ds) || dim_is_one(ds) {
    let bit = dim_is_one(ds)
    let bs : Array[DEquivBranchValue] = []
    for br in generic.branches {
      bs.push(
        dequiv_branch_value(
          face_simplify(face_subst(br.face, dlevel, bit)),
          br.ty,
          br.equiv,
        ),
      )
    }
    let dom_face = glue_equiv_domain_face(bs)
    DGlueEquivParts::{
      branches: bs,
      face: dom_face,
      base: if face_is_top_sem(dom_face) {
        generic.base
      } else {
        parts.base
      },
      level: generic.level,
    }
  } else {
    generic
  }
}

///|
fn glue_equiv_sym_sect_path(
  br : DEquivBranchValue,
  base : DValue,
  a_raw : DValue,
) -> (Dim) -> DValue {
  let sect = equiv_sect_value(br.equiv, br.ty, base)
  let p = dapp_typed(sect, a_raw, base)
  k => dapp_dim(p, dim_simplify(DNeg(k)))
}

///|
pub fn comp_glue_equiv_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  let a_line = (j : Dim) => glue_equiv_endpoint_parts(line, j, dlevel).base
  let src = glue_equiv_endpoint_parts(line, DZero, dlevel)
  let tgt = glue_equiv_endpoint_parts(line, DOne, dlevel)
  let snd_branches = dsystem_map(branches, p => {
    j => glue_equiv_base_of(glue_equiv_parts_at(line, j), p(j))
  })
  let base0 = glue_equiv_base_of(src, base)
  let a_raw = comp_value(a_line, snd_branches, base0, dlevel)
  let count = tgt.branches.length()
  let partial0 = glue_equiv_partial_values(src, base)
  let fills : Array[(Dim) -> DValue] = []
  let t_outs : Array[DValue] = []
  let src_actives : Array[Bool] = []
  for idx in 0..<count {
    let br_tgt = tgt.branches[idx]
    let src_active = idx < src.branches.length() &&
      !face_is_bot_sem(src.branches[idx].face)
    src_actives.push(src_active)
    if src_active {
      let t_line = (j : Dim) => {
        let pj = glue_equiv_parts_at(line, j)
        if idx < pj.branches.length() {
          pj.branches[idx].ty
        } else {
          pj.base
        }
      }
      let t_branches = dsystem_map(branches, p => {
        j => {
          let pj = glue_equiv_parts_at(line, j)
          let pvs = glue_equiv_partial_values(pj, p(j))
          if idx < pvs.length() {
            pvs[idx]
          } else {
            glue_equiv_base_of(pj, p(j))
          }
        }
      })
      let t_base = if idx < partial0.length() {
        partial0[idx]
      } else {
        equiv_inv_fun_value(
          src.branches[idx].equiv,
          src.branches[idx].ty,
          src.base,
          base0,
        )
      }
      let t_fill = fill_value(t_line, t_branches, t_base, dlevel)
      fills.push(t_fill)
      t_outs.push(t_fill(DOne))
    } else {
      let t_val = equiv_inv_fun_value(br_tgt.equiv, br_tgt.ty, tgt.base, a_raw)
      fills.push(_ => t_val)
      t_outs.push(t_val)
    }
  }
  let a_out = if count == 0 {
    a_raw
  } else {
    let correction_branches : Array[DTubeBranch] = []
    for idx in 0..<count {
      let br_tgt = tgt.branches[idx]
      if src_actives[idx] {
        let t_fill = fills[idx]
        let correction = (k : Dim) => {
          let pk = glue_equiv_parts_at(line, k)
          let down = if idx < pk.branches.length() {
            let brk = pk.branches[idx]
            equiv_fun_value(brk.equiv, brk.ty, pk.base, t_fill(k))
          } else {
            t_fill(k)
          }
          coe_value(a_line, k, DOne, down, dlevel)
        }
        correction_branches.push(tube_branch(br_tgt.face, correction))
      } else {
        let corr = glue_equiv_sym_sect_path(br_tgt, tgt.base, a_raw)
        correction_branches.push(tube_branch(br_tgt.face, corr))
      }
    }
    hcomp_value(a_line(DOne), dsystem_of(correction_branches), a_raw, dlevel)
  }
  if count == 0 || face_is_bot_sem(tgt.face) {
    a_out
  } else {
    let top = glue_equiv_top_index(tgt)
    if top >= 0 && top < t_outs.length() {
      t_outs[top]
    } else {
      DVPair(glue_equiv_store_partial(tgt, t_outs), a_out)
    }
  }
}

///|
pub fn check_computational_univalence() -> Bool {
  // 1. Term-level DPathToEquiv & DUa type-checking in dependent kernel
  let ua_not = DTerm::DUa(bool_not_equiv_term())
  let eqv_back = DTerm::DPathToEquiv(ua_not)
  let eqv_bb_dt = DTerm::DEquivTy(DBoolTy, DBoolTy)
  if !dep_check_closed(eqv_back, eqv_bb_dt) {
    return false
  }
  let roundtrip_app = DTerm::DApp(DTerm::DEquivFwd(eqv_back), DBoolLit(true))
  if dep_nf_closed(roundtrip_app, DBoolTy) != Some(DTerm::DBoolLit(false)) {
    return false
  }
  let inv_app = DTerm::DApp(DTerm::DEquivBwd(eqv_back), DBoolLit(false))
  if dep_nf_closed(inv_app, DBoolTy) != Some(DTerm::DBoolLit(true)) {
    return false
  }

  // 2. Open / neutral computational univalence (`A, B : U`, `e : Equiv A B`, `x : A`, `y : B`, `p : Path U A B`)
  let univ0 = DValue::DVUniv(0)
  let ty_a = reflect_var(0, univ0)
  let ty_b = reflect_var(1, univ0)
  let eq_ab = DValue::DVEquivTy(ty_a, ty_b, 0)
  let neu_e = reflect_var(2, eq_ab)
  let neu_x = reflect_var(3, ty_a)
  let path_u_aa = DValue::DVPathTy(_ => univ0, ty_a, ty_a)
  let path_u_ab = DValue::DVPathTy(_ => univ0, ty_a, ty_b)
  let neu_p = reflect_var(4, path_u_ab)
  let neu_y = reflect_var(5, ty_b)

  let ua_id_a = ua_id_path_value(ty_a, 0, 0)
  let p_id_a = ua_value(equiv_id_value(ty_a), ty_a, ty_a, 0)
  let refl_a = DValue::DVPathLam(_ => ty_a)
  if !conv_at(1, 0, path_u_aa, dapp_dim(ua_id_a, DZero), p_id_a) ||
    !conv_at(1, 0, path_u_aa, dapp_dim(ua_id_a, DOne), refl_a) {
    return false
  }

  let beta_ab = ua_beta_path_value(neu_e, ty_a, ty_b, 0, neu_x, 0)
  let coe_ab = coe_value(
    ua_line_value(neu_e, ty_a, ty_b, 0),
    DZero,
    DOne,
    neu_x,
    0,
  )
  if !conv_at(4, 0, ty_b, dapp_dim(beta_ab, DZero), coe_ab) ||
    !conv_at(
      4,
      0,
      ty_b,
      dapp_dim(beta_ab, DOne),
      equiv_fun_value(neu_e, ty_a, ty_b, neu_x),
    ) {
    return false
  }

  let beta_inv = ua_beta_inv_path_value(neu_e, ty_a, ty_b, 0, neu_y, 0)
  let coe_ba = coe_value(
    ua_line_value(neu_e, ty_a, ty_b, 0),
    DOne,
    DZero,
    neu_y,
    0,
  )
  if !conv_at(6, 0, ty_a, dapp_dim(beta_inv, DZero), coe_ba) ||
    !conv_at(
      6,
      0,
      ty_a,
      dapp_dim(beta_inv, DOne),
      equiv_inv_fun_value(neu_e, ty_a, ty_b, neu_y),
    ) {
    return false
  }

  let eta_p = ua_eta_path_value(d => dapp_dim(neu_p, d), ty_a, ty_b, 0, 0)
  let pte_p = path_to_equiv_value(d => dapp_dim(neu_p, d), ty_a, ty_b, 0, 0)
  let ua_pte_p = ua_value(pte_p, ty_a, ty_b, 0)
  if !conv_at(5, 0, path_u_ab, dapp_dim(eta_p, DZero), ua_pte_p) ||
    !conv_at(5, 0, path_u_ab, dapp_dim(eta_p, DOne), neu_p) {
    return false
  }

  let retr_e = path_to_equiv_ua_beta_path_value(neu_e, ty_a, ty_b, 0, 0)
  let pte_ua_e = path_to_equiv_value(
    ua_line_value(neu_e, ty_a, ty_b, 0),
    ty_a,
    ty_b,
    0,
    0,
  )
  conv_at(4, 0, eq_ab, dapp_dim(retr_e, DZero), pte_ua_e) &&
  conv_at(4, 0, eq_ab, dapp_dim(retr_e, DOne), neu_e)
}
