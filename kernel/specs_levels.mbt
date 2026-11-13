///|
// Universe level expressions, inductive / HIT schema specifications,
// subcube restriction helpers, face-relative conversion, and term utilities.

///|
#derive(Debug, Eq)
pub(all) enum DLevelExpr {
  DLevelConst(Int32)
  DLevelVar(Int32)
  DLevelSucc(DLevelExpr)
  DLevelMax(DLevelExpr, DLevelExpr)
}

///|
pub extend DLevelExpr with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DLevelExpr with Eq::{not_equal, equal}

///|
#derive(Debug, Eq)
pub(all) struct DConstructorSpec {
  name : String
  arity : Int32
  result_indices : Array[DTerm]
}

///|
pub extend DConstructorSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DConstructorSpec with Eq::{not_equal, equal}

///|
#derive(Debug, Eq)
pub(all) struct DInductiveSpec {
  name : String
  num_params : Int32
  num_indices : Int32
  constructors : Array[DConstructorSpec]
}

///|
pub extend DInductiveSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DInductiveSpec with Eq::{not_equal, equal}

///|
#derive(Debug, Eq)
pub(all) struct DHitCellSpec {
  name : String
  arity : Int32
  dim_arity : Int32
  result_indices : Array[DTerm]
}

///|
pub extend DHitCellSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DHitCellSpec with Eq::{not_equal, equal}

///|
#derive(Debug, Eq)
pub(all) struct DHitSpec {
  name : String
  num_params : Int32
  num_indices : Int32
  cells : Array[DHitCellSpec]
}

///|
pub extend DHitSpec with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend DHitSpec with Eq::{not_equal, equal}

///|
pub fn inductive_result_indices(
  ctor : DConstructorSpec,
  params : Array[DValue],
  args : Array[DValue],
) -> Array[DValue] {
  let env = denv_extend(args, denv_extend(params, denv_empty()))
  let out : Array[DValue] = []
  for idx_t in ctor.result_indices {
    out.push(deval_dim(idx_t, env, ddim_empty()))
  }
  out
}

///|
pub fn hit_cell_result_indices(
  spec : DHitSpec,
  c : Int32,
  params : Array[DValue],
  args : Array[DValue],
) -> Array[DValue] {
  if c < 0 || c >= spec.cells.length() {
    return []
  }
  let cell = spec.cells[c]
  let env = denv_extend(args, denv_extend(params, denv_empty()))
  let out : Array[DValue] = []
  for idx_t in cell.result_indices {
    out.push(deval_dim(idx_t, env, ddim_empty()))
  }
  out
}

///|
pub fn cubical_face_subcubes(face : Face, nvars : Int32) -> Array[Array[Int32]] {
  bdd_satisfying_cubes(bdd_of_face(face, nvars), nvars)
}

///|
pub fn cube_dim_env(asgn : Array[Int32]) -> DDimEnv {
  let dims : Array[Dim] = []
  for i in 0..<asgn.length() {
    let d = if asgn[i] == 0 {
      Dim::DZero
    } else if asgn[i] == 1 {
      Dim::DOne
    } else {
      Dim::DVar(i)
    }
    dims.push(d)
  }
  ddim_extend(dims, ddim_empty())
}

///|
fn reeval_under_dim_sub(
  env : DEnv,
  level : Int32,
  sub_dl : Int32,
  asgn : Array[Int32],
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  let sub_dim_env = cube_dim_env(asgn)
  let mut env_sub = denv_empty()
  for lvl in 0..<level {
    let sub_ty = DVUniv(0)
    let sub_var = reflect_var(lvl, sub_ty)
    let sub_val = match denv_at(env, level - 1 - lvl) {
      Some(orig_v) => {
        let vt = quote_at(lvl + 1, sub_dl, DVUniv(0), orig_v)
        deval_dim(vt, denv_cons(sub_var, env_sub), sub_dim_env)
      }
      None => sub_var
    }
    env_sub = denv_cons(sub_val, env_sub)
  }
  let ty_term = quote_ty(level, sub_dl, ty)
  let ty_sub = deval_dim(ty_term, env_sub, sub_dim_env)
  let a_term = quote_at(level, sub_dl, ty, a)
  let b_term = quote_at(level, sub_dl, ty, b)
  let a_sub = deval_dim(a_term, env_sub, sub_dim_env)
  let b_sub = deval_dim(b_term, env_sub, sub_dim_env)
  conv_at(level, sub_dl, ty_sub, a_sub, b_sub)
}

///|
pub fn conv_at_under_face(
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  if conv_at(level, dlevel, ty, a, b) {
    return true
  }
  if face_is_bot_sem(face) {
    return true
  }
  let fvars = face_nvars_sem(face)
  let sub_dl = if dlevel > fvars { dlevel } else { fvars }
  let subcubes = cubical_face_subcubes(face, sub_dl)
  if subcubes.length() == 0 {
    return false
  }
  for asgn in subcubes {
    if !reeval_under_dim_sub(denv_empty(), level, sub_dl, asgn, ty, a, b) {
      return false
    }
  }
  true
}

///|
fn conv_at_under_face_in_env(
  env : DEnv,
  level : Int32,
  dlevel : Int32,
  face : Face,
  ty : DValue,
  a : DValue,
  b : DValue,
) -> Bool {
  if conv_at(level, dlevel, ty, a, b) {
    return true
  }
  if face_is_bot_sem(face) {
    return true
  }
  let fvars = face_nvars_sem(face)
  let sub_dl = if dlevel > fvars { dlevel } else { fvars }
  let subcubes = cubical_face_subcubes(face, sub_dl)
  if subcubes.length() == 0 {
    return false
  }
  for asgn in subcubes {
    if !reeval_under_dim_sub(env, level, sub_dl, asgn, ty, a, b) {
      return false
    }
  }
  true
}

///|
pub fn dsystem_compatible_with_base_in(
  env : DEnv,
  level : Int32,
  dlevel : Int32,
  line_fn : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
) -> Bool {
  let n = branches.branches.length()
  let ty0 = line_fn(DZero)
  for i in 0..<n {
    let br = branches.branches[i]
    if !conv_at_under_face_in_env(
        env,
        level,
        dlevel,
        br.face,
        ty0,
        (br.path)(DZero),
        base,
      ) {
      return false
    }
  }
  let fd = Dim::DVar(dlevel)
  let ty_fd = line_fn(fd)
  for i in 0..<n {
    for j in (i + 1)..<n {
      let bi = branches.branches[i]
      let bj = branches.branches[j]
      let overlap = face_simplify(FAnd(bi.face, bj.face))
      if !face_is_bot_sem(overlap) {
        if !conv_at_under_face_in_env(
            env,
            level,
            dlevel + 1,
            overlap,
            ty_fd,
            (bi.path)(fd),
            (bj.path)(fd),
          ) {
          return false
        }
      }
    }
  }
  true
}

///|
pub fn dv_is_bool_dep(v : DValue, expected : Bool) -> Bool {
  match force_value(v) {
    DVBool(b) => b == expected
    _ => false
  }
}

///|
pub fn dterm_children(t : DTerm) -> Array[DTerm] {
  match t {
    DTVar(_)
    | DUniv(_)
    | DUnivLevel(_)
    | DBoolTy
    | DUnitTy
    | DBoolLit(_)
    | DUnitLit
    | DNatTy
    | DNatZero
    | DNil
    | DCircleTy
    | DCircleBase
    | DCircleLoop
    | DTorusTy
    | DTorusBase
    | DTorusLoopA
    | DTorusLoopB
    | DTorusSquare => []
    DFst(a)
    | DSnd(a)
    | DLamDim(a)
    | DAppDim(a, _)
    | DSucc(a)
    | DListTy(a)
    | DEquivFwd(a)
    | DEquivBwd(a)
    | DEquivSect(a)
    | DEquivRetr(a)
    | DUa(a)
    | DPathToEquiv(a) => [a]
    DPi(a, b)
    | DSigma(a, b)
    | DLam(a, b)
    | DApp(a, b)
    | DPair(a, b)
    | DAnn(a, b)
    | DCons(a, b)
    | DEquivTy(a, b)
    | DCoe(a, _, _, b) => [a, b]
    DPathP(a, b, c) | DPath(a, b, c) | DTorusElim(a, b, c) => [a, b, c]
    DBoolElim(a, b, c, d)
    | DNatElim(a, b, c, d)
    | DListElim(a, b, c, d)
    | DCircleElim(a, b, c, d) => [a, b, c, d]
    DPartial(bs) => bs.map(b => b.body)
    DComp(line, tubes, base)
    | DHComp(line, tubes, base)
    | DHFill(line, tubes, base, _) => {
      let out = [line]
      for tb in tubes {
        out.push(tb.body)
      }
      out.push(base)
      out
    }
    DInductive(_, args) | DHitType(_, args) => args
    DIntro(_, _, ps, args) | DHitIntro(_, _, ps, args, _) => {
      let out : Array[DTerm] = []
      for x in ps {
        out.push(x)
      }
      for x in args {
        out.push(x)
      }
      out
    }
    DInductiveElim(_, m, cases, ps, ix, scrut)
    | DHitElim(_, m, cases, ps, ix, scrut) => {
      let out = [m]
      for x in cases {
        out.push(x)
      }
      for x in ps {
        out.push(x)
      }
      for x in ix {
        out.push(x)
      }
      out.push(scrut)
      out
    }
    DDecode(_, ps, ix, code) => {
      let out : Array[DTerm] = []
      for x in ps {
        out.push(x)
      }
      for x in ix {
        out.push(x)
      }
      out.push(code)
      out
    }
    DMkEquiv(a, b, f, g, s, r) => [a, b, f, g, s, r]
    DGlueEquiv(base, bs) => {
      let out = [base]
      for br in bs {
        out.push(br.ty)
        out.push(br.equiv)
      }
      out
    }
    DUnglueEquiv(term, base, bs) => {
      let out = [term, base]
      for br in bs {
        out.push(br.ty)
        out.push(br.equiv)
      }
      out
    }
  }
}
