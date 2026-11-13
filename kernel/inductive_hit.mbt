///|
// Evaluation, type inference, conversion, quoting, and Kan composition
// for schema-driven inductive types and higher inductive types.

///|
fn eval_term_array(
  ts : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> Array[DValue] {
  let out : Array[DValue] = []
  for t in ts {
    out.push(deval_dim(t, env, denv))
  }
  out
}

///|
fn split_params_indices(
  num_params : Int32,
  args : Array[DValue],
) -> (Array[DValue], Array[DValue]) {
  let ps : Array[DValue] = []
  let ix : Array[DValue] = []
  for i in 0..<args.length() {
    if i < num_params {
      ps.push(args[i])
    } else {
      ix.push(args[i])
    }
  }
  (ps, ix)
}

///|
fn apply_many(fn_val : DValue, args : Array[DValue]) -> DValue {
  let mut cur = fn_val
  for a in args {
    cur = dapp_typed(cur, a, DVUnitTy)
  }
  cur
}

///|
fn apply_many_dims(fn_val : DValue, dims : Array[Dim]) -> DValue {
  let mut cur = fn_val
  for d in dims {
    cur = dapp_dim(cur, d)
  }
  cur
}

///|
pub fn eval_inductive_type_term(
  spec : DInductiveSpec,
  args : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let vals = eval_term_array(args, env, denv)
  let (ps, ix) = split_params_indices(spec.num_params, vals)
  DVInductive(spec, ps, ix)
}

///|
pub fn eval_intro_term(
  spec : DInductiveSpec,
  ctor : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  DVIntro(
    spec,
    ctor,
    eval_term_array(params, env, denv),
    eval_term_array(args, env, denv),
  )
}

///|
fn apply_inductive_elim_val(
  spec : DInductiveSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVIntro(s, c, _, args) =>
      if s == spec && c >= 0 && c < cases.length() {
        apply_many(cases[c], args)
      } else {
        DVUnit
      }
    DVNeutral(DNComp(line, branches, base)) => {
      let scrut_fill = fill_value(line, branches, base, dlevel)
      let mapped = dsystem_map(branches, p => {
        d => {
          apply_inductive_elim_val(
            spec,
            motive,
            cases,
            params,
            indices,
            p(d),
            dlevel,
          )
        }
      })
      comp_value(
        d => motive(indices, scrut_fill(d)),
        mapped,
        apply_inductive_elim_val(
          spec, motive, cases, params, indices, base, dlevel,
        ),
        dlevel,
      )
    }
    DVNeutral(DNHComp(hty, branches, base)) => {
      let scrut_fill = hfill_value(hty, branches, base, dlevel)
      let mapped = dsystem_map(branches, p => {
        d => {
          apply_inductive_elim_val(
            spec,
            motive,
            cases,
            params,
            indices,
            p(d),
            dlevel,
          )
        }
      })
      comp_value(
        d => motive(indices, scrut_fill(d)),
        mapped,
        apply_inductive_elim_val(
          spec, motive, cases, params, indices, base, dlevel,
        ),
        dlevel,
      )
    }
    DVNeutral(n) =>
      DVNeutral(DNInductiveElim(spec, motive, cases, params, indices, n))
    _ => DVUnit
  }
}

///|
pub fn eval_inductive_elim_term(
  spec : DInductiveSpec,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  indices : Array[DTerm],
  scrut : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let motive_fn = fn(ixs : Array[DValue], x : DValue) -> DValue {
    deval_dim(motive, denv_cons(x, denv_extend(ixs, env)), denv)
  }
  apply_inductive_elim_val(
    spec,
    motive_fn,
    eval_term_array(cases, env, denv),
    eval_term_array(params, env, denv),
    eval_term_array(indices, env, denv),
    deval_dim(scrut, env, denv),
    ddim_len(denv),
  )
}

///|
pub fn eval_hit_type_term(
  spec : DHitSpec,
  args : Array[DTerm],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let vals = eval_term_array(args, env, denv)
  let (ps, ix) = split_params_indices(spec.num_params, vals)
  DVHitType(spec, ps, ix)
}

///|
pub fn eval_hit_intro_term(
  spec : DHitSpec,
  cell : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
  dims : Array[Dim],
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let edims : Array[Dim] = []
  for d in dims {
    edims.push(eval_dim_expr(d, denv))
  }
  DVHitCell(
    spec,
    cell,
    eval_term_array(params, env, denv),
    eval_term_array(args, env, denv),
    edims,
  )
}

///|
fn apply_hit_elim_val(
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DValue,
  dlevel : Int32,
) -> DValue {
  match force_value(scrut) {
    DVHitCell(s, c, _, args, dims) =>
      if s == spec && c >= 0 && c < cases.length() {
        apply_many_dims(apply_many(cases[c], args), dims)
      } else {
        DVUnit
      }
    DVNeutral(DNComp(line, branches, base)) => {
      let scrut_fill = fill_value(line, branches, base, dlevel)
      let mapped = dsystem_map(branches, p => {
        d => {
          apply_hit_elim_val(spec, motive, cases, params, indices, p(d), dlevel)
        }
      })
      comp_value(
        d => motive(indices, scrut_fill(d)),
        mapped,
        apply_hit_elim_val(spec, motive, cases, params, indices, base, dlevel),
        dlevel,
      )
    }
    DVNeutral(DNHComp(hty, branches, base)) => {
      let scrut_fill = hfill_value(hty, branches, base, dlevel)
      let mapped = dsystem_map(branches, p => {
        d => {
          apply_hit_elim_val(spec, motive, cases, params, indices, p(d), dlevel)
        }
      })
      comp_value(
        d => motive(indices, scrut_fill(d)),
        mapped,
        apply_hit_elim_val(spec, motive, cases, params, indices, base, dlevel),
        dlevel,
      )
    }
    DVNeutral(n) =>
      DVNeutral(DNHitElim(spec, motive, cases, params, indices, n))
    _ => DVUnit
  }
}

///|
pub fn eval_hit_elim_term(
  spec : DHitSpec,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  indices : Array[DTerm],
  scrut : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let motive_fn = fn(ixs : Array[DValue], x : DValue) -> DValue {
    deval_dim(motive, denv_cons(x, denv_extend(ixs, env)), denv)
  }
  apply_hit_elim_val(
    spec,
    motive_fn,
    eval_term_array(cases, env, denv),
    eval_term_array(params, env, denv),
    eval_term_array(indices, env, denv),
    deval_dim(scrut, env, denv),
    ddim_len(denv),
  )
}

///|
pub fn eval_decode_term(
  spec : DInductiveSpec,
  params : Array[DTerm],
  indices : Array[DTerm],
  code : DTerm,
  env : DEnv,
  denv : DDimEnv,
) -> DValue {
  let ps = eval_term_array(params, env, denv)
  let ix = eval_term_array(indices, env, denv)
  match force_value(deval_dim(code, env, denv)) {
    DVNeutral(n) => DVNeutral(DNDecode(spec, ps, ix, n))
    v => v
  }
}

///|
pub fn infer_inductive_type(
  spec : DInductiveSpec,
  args : Array[DTerm],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  let vals : Array[DValue] = []
  for a in args {
    match d_infer(a, ctx, env, denv) {
      Some(inf) => vals.push(inf.value)
      None => return None
    }
  }
  let (ps, ix) = split_params_indices(spec.num_params, vals)
  Some(DInfer::{ value: DVInductive(spec, ps, ix), ty: DVUniv(0), })
}

///|
pub fn infer_intro(
  spec : DInductiveSpec,
  ctor : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if ctor < 0 || ctor >= spec.constructors.length() {
    return None
  }
  let pvals : Array[DValue] = []
  for p in params {
    match d_infer(p, ctx, env, denv) {
      Some(inf) => pvals.push(inf.value)
      None => return None
    }
  }
  let avals : Array[DValue] = []
  for a in args {
    match d_infer(a, ctx, env, denv) {
      Some(inf) => avals.push(inf.value)
      None => return None
    }
  }
  let ix = inductive_result_indices(spec.constructors[ctor], pvals, avals)
  Some(DInfer::{
    value: DVIntro(spec, ctor, pvals, avals),
    ty: DVInductive(spec, pvals, ix),
  })
}

///|
pub fn infer_inductive_elim(
  spec : DInductiveSpec,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  indices : Array[DTerm],
  scrut : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  let pvals = eval_term_array(params, env, denv)
  let ixvals = eval_term_array(indices, env, denv)
  let scrut_ty = DVInductive(spec, pvals, ixvals)
  match d_check(scrut, scrut_ty, ctx, env, denv) {
    Some(sv) => {
      let mfn = fn(ixs : Array[DValue], x : DValue) -> DValue {
        deval_dim(motive, denv_cons(x, denv_extend(ixs, env)), denv)
      }
      let cvals = eval_term_array(cases, env, denv)
      Some(DInfer::{
        value: apply_inductive_elim_val(
          spec,
          mfn,
          cvals,
          pvals,
          ixvals,
          sv,
          ddim_len(denv),
        ),
        ty: mfn(ixvals, sv),
      })
    }
    None => None
  }
}

///|
pub fn infer_hit_type(
  spec : DHitSpec,
  args : Array[DTerm],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  let vals : Array[DValue] = []
  for a in args {
    match d_infer(a, ctx, env, denv) {
      Some(inf) => vals.push(inf.value)
      None => return None
    }
  }
  let (ps, ix) = split_params_indices(spec.num_params, vals)
  Some(DInfer::{ value: DVHitType(spec, ps, ix), ty: DVUniv(0), })
}

///|
pub fn infer_hit_intro(
  spec : DHitSpec,
  cell : Int32,
  params : Array[DTerm],
  args : Array[DTerm],
  dims : Array[Dim],
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  if cell < 0 || cell >= spec.cells.length() {
    return None
  }
  let pvals : Array[DValue] = []
  for p in params {
    match d_infer(p, ctx, env, denv) {
      Some(inf) => pvals.push(inf.value)
      None => return None
    }
  }
  let avals : Array[DValue] = []
  for a in args {
    match d_infer(a, ctx, env, denv) {
      Some(inf) => avals.push(inf.value)
      None => return None
    }
  }
  let edims : Array[Dim] = []
  for d in dims {
    edims.push(eval_dim_expr(d, denv))
  }
  let ix = hit_cell_result_indices(spec, cell, pvals, avals)
  Some(DInfer::{
    value: DVHitCell(spec, cell, pvals, avals, edims),
    ty: DVHitType(spec, pvals, ix),
  })
}

///|
pub fn infer_hit_elim(
  spec : DHitSpec,
  motive : DTerm,
  cases : Array[DTerm],
  params : Array[DTerm],
  indices : Array[DTerm],
  scrut : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  let pvals = eval_term_array(params, env, denv)
  let ixvals = eval_term_array(indices, env, denv)
  let scrut_ty = DVHitType(spec, pvals, ixvals)
  match d_check(scrut, scrut_ty, ctx, env, denv) {
    Some(sv) => {
      let mfn = fn(ixs : Array[DValue], x : DValue) -> DValue {
        deval_dim(motive, denv_cons(x, denv_extend(ixs, env)), denv)
      }
      let cvals = eval_term_array(cases, env, denv)
      Some(DInfer::{
        value: apply_hit_elim_val(
          spec,
          mfn,
          cvals,
          pvals,
          ixvals,
          sv,
          ddim_len(denv),
        ),
        ty: mfn(ixvals, sv),
      })
    }
    None => None
  }
}

///|
pub fn infer_decode(
  spec : DInductiveSpec,
  params : Array[DTerm],
  indices : Array[DTerm],
  code : DTerm,
  ctx : DEnv,
  env : DEnv,
  denv : DDimEnv,
) -> DInfer? {
  let pvals = eval_term_array(params, env, denv)
  let ixvals = eval_term_array(indices, env, denv)
  match d_infer(code, ctx, env, denv) {
    Some(inf) =>
      match force_value(inf.value) {
        DVNeutral(n) =>
          Some(DInfer::{
            value: DVNeutral(DNDecode(spec, pvals, ixvals, n)),
            ty: DVInductive(spec, pvals, ixvals),
          })
        v => Some(DInfer::{ value: v, ty: DVInductive(spec, pvals, ixvals), })
      }
    None => None
  }
}

///|
fn conv_val_arrays(
  level : Int32,
  dlevel : Int32,
  xs : Array[DValue],
  ys : Array[DValue],
) -> Bool {
  if xs.length() != ys.length() {
    return false
  }
  for i in 0..<xs.length() {
    if !conv_at(level, dlevel, DVUnitTy, xs[i], ys[i]) {
      return false
    }
  }
  true
}

///|
pub fn conv_inductive_type(
  level : Int32,
  dlevel : Int32,
  s1 : DInductiveSpec,
  p1 : Array[DValue],
  i1 : Array[DValue],
  s2 : DInductiveSpec,
  p2 : Array[DValue],
  i2 : Array[DValue],
) -> Bool {
  s1 == s2 &&
  conv_val_arrays(level, dlevel, p1, p2) &&
  conv_val_arrays(level, dlevel, i1, i2)
}

///|
pub fn conv_hit_type(
  level : Int32,
  dlevel : Int32,
  s1 : DHitSpec,
  p1 : Array[DValue],
  i1 : Array[DValue],
  s2 : DHitSpec,
  p2 : Array[DValue],
  i2 : Array[DValue],
) -> Bool {
  s1 == s2 &&
  conv_val_arrays(level, dlevel, p1, p2) &&
  conv_val_arrays(level, dlevel, i1, i2)
}

///|
pub fn conv_intro_at(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  _params : Array[DValue],
  a : DValue,
  b : DValue,
) -> Bool {
  match (force_value(a), force_value(b)) {
    (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
    (DVIntro(s1, c1, p1, a1), DVIntro(s2, c2, p2, a2)) =>
      s1 == spec &&
      s2 == spec &&
      c1 == c2 &&
      conv_val_arrays(level, dlevel, p1, p2) &&
      conv_val_arrays(level, dlevel, a1, a2)
    _ => false
  }
}

///|
fn normalize_hit_cell_for_conv(
  spec : DHitSpec,
  c : Int32,
  dims : Array[Dim],
) -> (Int32, Array[Dim]) {
  if spec.name == "CircleHIT" && c == 1 && dims.length() == 1 {
    let s = dim_simplify(dims[0])
    if dim_is_zero(s) || dim_is_one(s) {
      return (0, [])
    }
    return (1, [s])
  }
  (c, dims)
}

///|
pub fn conv_hit_cell_at(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  _params : Array[DValue],
  a : DValue,
  b : DValue,
) -> Bool {
  match (force_value(a), force_value(b)) {
    (DVNeutral(x), DVNeutral(y)) => conv_neutral(level, dlevel, x, y)
    (DVHitCell(s1, c1, p1, a1, d1), DVHitCell(s2, c2, p2, a2, d2)) => {
      let (nc1, nd1) = normalize_hit_cell_for_conv(s1, c1, d1)
      let (nc2, nd2) = normalize_hit_cell_for_conv(s2, c2, d2)
      if s1 != spec || s2 != spec || nc1 != nc2 || nd1.length() != nd2.length() {
        return false
      }
      if !conv_val_arrays(level, dlevel, p1, p2) ||
        !conv_val_arrays(level, dlevel, a1, a2) {
        return false
      }
      for k in 0..<nd1.length() {
        if !dim_eq_demorgan(nd1[k], nd2[k]) {
          return false
        }
      }
      true
    }
    _ => false
  }
}

///|
pub fn conv_inductive_elim_neutral(
  level : Int32,
  dlevel : Int32,
  s1 : DInductiveSpec,
  m1 : (Array[DValue], DValue) -> DValue,
  c1 : Array[DValue],
  p1 : Array[DValue],
  i1 : Array[DValue],
  n1 : DNeutral,
  s2 : DInductiveSpec,
  m2 : (Array[DValue], DValue) -> DValue,
  c2 : Array[DValue],
  p2 : Array[DValue],
  i2 : Array[DValue],
  n2 : DNeutral,
) -> Bool {
  s1 == s2 &&
  conv_neutral(level, dlevel, n1, n2) &&
  conv_val_arrays(level, dlevel, p1, p2) &&
  conv_val_arrays(level, dlevel, i1, i2) &&
  conv_val_arrays(level, dlevel, c1, c2) &&
  conv_ty(
    level + 1,
    dlevel,
    m1(i1, DVNeutral(DNVar(level))),
    m2(i2, DVNeutral(DNVar(level))),
  )
}

///|
pub fn conv_hit_elim_neutral(
  level : Int32,
  dlevel : Int32,
  s1 : DHitSpec,
  m1 : (Array[DValue], DValue) -> DValue,
  c1 : Array[DValue],
  p1 : Array[DValue],
  i1 : Array[DValue],
  n1 : DNeutral,
  s2 : DHitSpec,
  m2 : (Array[DValue], DValue) -> DValue,
  c2 : Array[DValue],
  p2 : Array[DValue],
  i2 : Array[DValue],
  n2 : DNeutral,
) -> Bool {
  s1 == s2 &&
  conv_neutral(level, dlevel, n1, n2) &&
  conv_val_arrays(level, dlevel, p1, p2) &&
  conv_val_arrays(level, dlevel, i1, i2) &&
  conv_val_arrays(level, dlevel, c1, c2) &&
  conv_ty(
    level + 1,
    dlevel,
    m1(i1, DVNeutral(DNVar(level))),
    m2(i2, DVNeutral(DNVar(level))),
  )
}

///|
pub fn conv_decode_neutral(
  level : Int32,
  dlevel : Int32,
  s1 : DInductiveSpec,
  p1 : Array[DValue],
  i1 : Array[DValue],
  n1 : DNeutral,
  s2 : DInductiveSpec,
  p2 : Array[DValue],
  i2 : Array[DValue],
  n2 : DNeutral,
) -> Bool {
  s1 == s2 &&
  conv_neutral(level, dlevel, n1, n2) &&
  conv_val_arrays(level, dlevel, p1, p2) &&
  conv_val_arrays(level, dlevel, i1, i2)
}

///|
fn quote_val_array(
  level : Int32,
  dlevel : Int32,
  xs : Array[DValue],
) -> Array[DTerm] {
  let out : Array[DTerm] = []
  for x in xs {
    out.push(quote_at(level, dlevel, DVUnitTy, x))
  }
  out
}

///|
pub fn quote_inductive_type(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> DTerm {
  let args = quote_val_array(level, dlevel, params)
  for ix in indices {
    args.push(quote_at(level, dlevel, DVUnitTy, ix))
  }
  DInductive(spec, args)
}

///|
pub fn quote_hit_type(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  params : Array[DValue],
  indices : Array[DValue],
) -> DTerm {
  let args = quote_val_array(level, dlevel, params)
  for ix in indices {
    args.push(quote_at(level, dlevel, DVUnitTy, ix))
  }
  DHitType(spec, args)
}

///|
pub fn quote_intro_at(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  params : Array[DValue],
  ty : DValue,
  v : DValue,
) -> DTerm {
  match force_value(v) {
    DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
    DVIntro(s, c, ps, args) =>
      DIntro(
        s,
        c,
        quote_val_array(level, dlevel, ps),
        quote_val_array(level, dlevel, args),
      )
    _ => DIntro(spec, 0, quote_val_array(level, dlevel, params), [])
  }
}

///|
pub fn quote_hit_cell_at(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  params : Array[DValue],
  ty : DValue,
  v : DValue,
) -> DTerm {
  match force_value(v) {
    DVNeutral(n) => quote_dneutral(level, dlevel, n, ty)
    DVHitCell(s, c, ps, args, dims) => {
      let qdims : Array[Dim] = []
      for d in dims {
        qdims.push(dim_quote(d, dlevel))
      }
      DHitIntro(
        s,
        c,
        quote_val_array(level, dlevel, ps),
        quote_val_array(level, dlevel, args),
        qdims,
      )
    }
    _ => DHitIntro(spec, 0, quote_val_array(level, dlevel, params), [], [])
  }
}

///|
pub fn quote_inductive_elim_neutral(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DNeutral,
) -> DTerm {
  let ty = DVInductive(spec, params, indices)
  let qm = quote_ty(level + 1, dlevel, motive(indices, DVNeutral(DNVar(level))))
  DInductiveElim(
    spec,
    qm,
    quote_val_array(level, dlevel, cases),
    quote_val_array(level, dlevel, params),
    quote_val_array(level, dlevel, indices),
    quote_dneutral(level, dlevel, scrut, ty),
  )
}

///|
pub fn quote_hit_elim_neutral(
  level : Int32,
  dlevel : Int32,
  spec : DHitSpec,
  motive : (Array[DValue], DValue) -> DValue,
  cases : Array[DValue],
  params : Array[DValue],
  indices : Array[DValue],
  scrut : DNeutral,
) -> DTerm {
  let ty = DVHitType(spec, params, indices)
  let qm = quote_ty(level + 1, dlevel, motive(indices, DVNeutral(DNVar(level))))
  DHitElim(
    spec,
    qm,
    quote_val_array(level, dlevel, cases),
    quote_val_array(level, dlevel, params),
    quote_val_array(level, dlevel, indices),
    quote_dneutral(level, dlevel, scrut, ty),
  )
}

///|
pub fn quote_decode_neutral(
  level : Int32,
  dlevel : Int32,
  spec : DInductiveSpec,
  params : Array[DValue],
  indices : Array[DValue],
  code : DNeutral,
) -> DTerm {
  DDecode(
    spec,
    quote_val_array(level, dlevel, params),
    quote_val_array(level, dlevel, indices),
    quote_dneutral(level, dlevel, code, DVUnitTy),
  )
}

///|
pub fn comp_inductive_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  _dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    match force_value(base) {
      DVIntro(_, _, _, _) => base
      _ => DVNeutral(DNComp(line, branches, base))
    }
  } else {
    DVNeutral(DNComp(line, branches, base))
  }
}

///|
fn is_hit_base_point(v : DValue) -> Bool {
  match force_value(v) {
    DVHitCell(s, c, _, _, ds) => {
      let (nc, _) = normalize_hit_cell_for_conv(s, c, ds)
      s.name == "CircleHIT" && nc == 0
    }
    _ => false
  }
}

///|
pub fn comp_hit_value(
  line : (Dim) -> DValue,
  branches : DSystem,
  base : DValue,
  dlevel : Int32,
) -> DValue {
  if branches.branches.length() == 0 {
    match force_value(base) {
      DVHitCell(_, _, _, _, _) => base
      _ => DVNeutral(DNComp(line, branches, base))
    }
  } else {
    let mut all_base = is_hit_base_point(base)
    for br in branches.branches {
      if !is_hit_base_point((br.path)(Dim::DVar(dlevel))) {
        all_base = false
      }
    }
    if all_base {
      base
    } else {
      DVNeutral(DNComp(line, branches, base))
    }
  }
}
