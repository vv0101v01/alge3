///|
// De Morgan dimension algebra, cubical faces, and canonical ROBDDs.

///|
#derive(Debug, Eq)
pub(all) enum Dim {
  DZero
  DOne
  DVar(Int32)
  DNeg(Dim)
  DAnd(Dim, Dim)
  DOr(Dim, Dim)
}

///|
pub extend Dim with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Dim with Eq::{not_equal, equal}

///|
#derive(Debug, Eq)
pub(all) enum Face {
  FTop
  FBot
  FEq0(Dim)
  FEq1(Dim)
  FAnd(Face, Face)
  FOr(Face, Face)
}

///|
pub extend Face with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Face with Eq::{not_equal, equal}

///|
#derive(Debug, Eq)
pub(all) enum Bdd {
  BddZero
  BddOne
  BddNode(Int32, Bdd, Bdd)
}

///|
pub extend Bdd with @moonbitlang/core/debug.Debug::{to_repr}

///|
pub extend Bdd with Eq::{not_equal, equal}

///|
pub struct BddManager {
  dummy : Int32
}

///|
pub fn bdd_manager_new() -> BddManager {
  BddManager::{ dummy: 0, }
}

///|
pub fn pow2(n : Int32) -> Int32 {
  if n <= 0 {
    1
  } else {
    let mut acc = 1
    for _i in 0..<n {
      acc = acc * 2
    }
    acc
  }
}

///|
pub fn contains_int(xs : Array[Int32], v : Int32) -> Bool {
  for i in 0..<xs.length() {
    if xs[i] == v {
      return true
    }
  }
  false
}

///|
pub fn sort_ints(xs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in xs {
    if !contains_int(out, x) {
      out.push(x)
    }
  }
  let n = out.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if out[j] < out[i] {
        let tmp = out[i]
        out[i] = out[j]
        out[j] = tmp
      }
    }
  }
  out
}

///|
pub fn assignment_of_mask(mask : Int32, nvars : Int32) -> Array[Bool] {
  let out : Array[Bool] = []
  for i in 0..<nvars {
    out.push(((mask >> i) & 1) != 0)
  }
  out
}

///|
pub fn eval_dim(d : Dim, vals : Array[Double]) -> Double {
  match d {
    DZero => 0.0
    DOne => 1.0
    DVar(i) => if i >= 0 && i < vals.length() { vals[i] } else { 0.0 }
    DNeg(a) => 1.0 - eval_dim(a, vals)
    DAnd(a, b) => {
      let va = eval_dim(a, vals)
      let vb = eval_dim(b, vals)
      if va < vb {
        va
      } else {
        vb
      }
    }
    DOr(a, b) => {
      let va = eval_dim(a, vals)
      let vb = eval_dim(b, vals)
      if va > vb {
        va
      } else {
        vb
      }
    }
  }
}

///|
pub fn dim_vars_into(d : Dim, acc : Array[Int32]) -> Unit {
  match d {
    DZero | DOne => ()
    DVar(i) => if !contains_int(acc, i) { acc.push(i) }
    DNeg(a) => dim_vars_into(a, acc)
    DAnd(a, b) | DOr(a, b) => {
      dim_vars_into(a, acc)
      dim_vars_into(b, acc)
    }
  }
}

///|
pub fn dim_nvars_sem(d : Dim) -> Int32 {
  let vars : Array[Int32] = []
  dim_vars_into(d, vars)
  let mut max_v = -1
  for v in vars {
    if v > max_v {
      max_v = v
    }
  }
  if max_v < 0 {
    0
  } else {
    max_v + 1
  }
}

///|
fn dim_push_neg(d : Dim, neg : Bool) -> Dim {
  match d {
    DZero => if neg { DOne } else { DZero }
    DOne => if neg { DZero } else { DOne }
    DVar(i) => if neg { DNeg(DVar(i)) } else { DVar(i) }
    DNeg(a) => dim_push_neg(a, !neg)
    DAnd(a, b) =>
      if neg {
        DOr(dim_push_neg(a, true), dim_push_neg(b, true))
      } else {
        DAnd(dim_push_neg(a, false), dim_push_neg(b, false))
      }
    DOr(a, b) =>
      if neg {
        DAnd(dim_push_neg(a, true), dim_push_neg(b, true))
      } else {
        DOr(dim_push_neg(a, false), dim_push_neg(b, false))
      }
  }
}

///|
fn dim_simp_inner(d : Dim) -> Dim {
  match d {
    DZero | DOne | DVar(_) => d
    DNeg(DVar(i)) => DNeg(DVar(i))
    DNeg(x) => dim_simp_inner(dim_push_neg(x, true))
    DAnd(a0, b0) => {
      let a = dim_simp_inner(a0)
      let b = dim_simp_inner(b0)
      match (a, b) {
        (DZero, _) | (_, DZero) => DZero
        (DOne, x) | (x, DOne) => x
        _ => if a == b { a } else { DAnd(a, b) }
      }
    }
    DOr(a0, b0) => {
      let a = dim_simp_inner(a0)
      let b = dim_simp_inner(b0)
      match (a, b) {
        (DOne, _) | (_, DOne) => DOne
        (DZero, x) | (x, DZero) => x
        _ => if a == b { a } else { DOr(a, b) }
      }
    }
  }
}

///|
pub fn dim_simplify(d : Dim) -> Dim {
  dim_simp_inner(dim_push_neg(d, false))
}

///|
pub fn dim_subst(d : Dim, v : Int32, bit : Bool) -> Dim {
  fn go(x : Dim) -> Dim {
    match x {
      DZero => DZero
      DOne => DOne
      DVar(i) => if i == v { if bit { DOne } else { DZero } } else { DVar(i) }
      DNeg(a) => DNeg(go(a))
      DAnd(a, b) => DAnd(go(a), go(b))
      DOr(a, b) => DOr(go(a), go(b))
    }
  }
  dim_simplify(go(d))
}

// ---------------------------------------------------------------------------
// Free De Morgan DNF canonicalization for `dim_eq_demorgan`
// ---------------------------------------------------------------------------
// Literals encoded as Int32: positive (v + 1) for v, negative -(v + 1) for ¬v.

///|
fn lit_subset(a : Array[Int32], b : Array[Int32]) -> Bool {
  for x in a {
    if !contains_int(b, x) {
      return false
    }
  }
  true
}

///|
fn cmp_conj(a : Array[Int32], b : Array[Int32]) -> Int32 {
  if a.length() != b.length() {
    if a.length() < b.length() {
      -1
    } else {
      1
    }
  } else {
    for i in 0..<a.length() {
      if a[i] != b[i] {
        return if a[i] < b[i] { -1 } else { 1 }
      }
    }
    0
  }
}

///|
fn dnf_canon(terms : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let cleaned : Array[Array[Int32]] = []
  for t in terms {
    cleaned.push(sort_ints(t))
  }
  let kept : Array[Array[Int32]] = []
  for i in 0..<cleaned.length() {
    let ti = cleaned[i]
    let mut absorbed = false
    for j in 0..<cleaned.length() {
      if i != j {
        let tj = cleaned[j]
        if lit_subset(tj, ti) {
          if !lit_subset(ti, tj) || j < i {
            absorbed = true
            break
          }
        }
      }
    }
    if !absorbed {
      kept.push(ti)
    }
  }
  let n = kept.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if cmp_conj(kept[j], kept[i]) < 0 {
        let tmp = kept[i]
        kept[i] = kept[j]
        kept[j] = tmp
      }
    }
  }
  kept
}

///|
fn dnf_and(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for ca in a {
    for cb in b {
      let merged : Array[Int32] = []
      for x in ca {
        merged.push(x)
      }
      for x in cb {
        merged.push(x)
      }
      out.push(merged)
    }
  }
  dnf_canon(out)
}

///|
fn dnf_or(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for c in a {
    out.push(c)
  }
  for c in b {
    out.push(c)
  }
  dnf_canon(out)
}

///|
fn dim_dnf(d : Dim, neg : Bool) -> Array[Array[Int32]] {
  match d {
    DZero => if neg { [[]] } else { [] }
    DOne => if neg { [] } else { [[]] }
    DVar(i) => [[if neg { -(i + 1) } else { i + 1 }]]
    DNeg(a) => dim_dnf(a, !neg)
    DAnd(a, b) =>
      if neg {
        dnf_or(dim_dnf(a, true), dim_dnf(b, true))
      } else {
        dnf_and(dim_dnf(a, false), dim_dnf(b, false))
      }
    DOr(a, b) =>
      if neg {
        dnf_and(dim_dnf(a, true), dim_dnf(b, true))
      } else {
        dnf_or(dim_dnf(a, false), dim_dnf(b, false))
      }
  }
}

///|
pub fn dim_eq_demorgan(a : Dim, b : Dim) -> Bool {
  dim_dnf(a, false) == dim_dnf(b, false)
}

// ---------------------------------------------------------------------------
// ROBDD operations
// ---------------------------------------------------------------------------

///|
fn bdd_node(v : Int32, lo : Bdd, hi : Bdd) -> Bdd {
  if lo == hi {
    lo
  } else {
    BddNode(v, lo, hi)
  }
}

///|
pub fn bdd_not(b : Bdd) -> Bdd {
  match b {
    BddZero => BddOne
    BddOne => BddZero
    BddNode(v, lo, hi) => bdd_node(v, bdd_not(lo), bdd_not(hi))
  }
}

///|
pub fn bdd_and(a : Bdd, b : Bdd) -> Bdd {
  match (a, b) {
    (BddZero, _) | (_, BddZero) => BddZero
    (BddOne, x) | (x, BddOne) => x
    (BddNode(va, loa, hia), BddNode(vb, lob, hib)) =>
      if va == vb {
        bdd_node(va, bdd_and(loa, lob), bdd_and(hia, hib))
      } else if va < vb {
        bdd_node(va, bdd_and(loa, b), bdd_and(hia, b))
      } else {
        bdd_node(vb, bdd_and(a, lob), bdd_and(a, hib))
      }
  }
}

///|
pub fn bdd_or(a : Bdd, b : Bdd) -> Bdd {
  match (a, b) {
    (BddOne, _) | (_, BddOne) => BddOne
    (BddZero, x) | (x, BddZero) => x
    (BddNode(va, loa, hia), BddNode(vb, lob, hib)) =>
      if va == vb {
        bdd_node(va, bdd_or(loa, lob), bdd_or(hia, hib))
      } else if va < vb {
        bdd_node(va, bdd_or(loa, b), bdd_or(hia, b))
      } else {
        bdd_node(vb, bdd_or(a, lob), bdd_or(a, hib))
      }
  }
}

///|
pub fn bdd_dag_true(_mgr : BddManager) -> Bdd {
  BddOne
}

///|
pub fn bdd_dag_var(_mgr : BddManager, v : Int32) -> Bdd {
  BddNode(v, BddZero, BddOne)
}

///|
pub fn bdd_dag_not(_mgr : BddManager, b : Bdd) -> Bdd {
  bdd_not(b)
}

///|
pub fn bdd_dag_or(_mgr : BddManager, a : Bdd, b : Bdd) -> Bdd {
  bdd_or(a, b)
}

///|
pub fn bdd_tree_cofactor(b : Bdd, v : Int32, val : Bool) -> Bdd {
  match b {
    BddZero | BddOne => b
    BddNode(bv, lo, hi) =>
      if bv == v {
        if val {
          hi
        } else {
          lo
        }
      } else if bv > v {
        b
      } else {
        bdd_node(
          bv,
          bdd_tree_cofactor(lo, v, val),
          bdd_tree_cofactor(hi, v, val),
        )
      }
  }
}

///|
fn bdd_of_dim(d : Dim) -> Bdd {
  match d {
    DZero => BddZero
    DOne => BddOne
    DVar(i) => BddNode(i, BddZero, BddOne)
    DNeg(a) => bdd_not(bdd_of_dim(a))
    DAnd(a, b) => bdd_and(bdd_of_dim(a), bdd_of_dim(b))
    DOr(a, b) => bdd_or(bdd_of_dim(a), bdd_of_dim(b))
  }
}

///|
pub fn dim_eq_sem(a : Dim, b : Dim) -> Bool {
  bdd_of_dim(a) == bdd_of_dim(b)
}

// ---------------------------------------------------------------------------
// Face operations
// ---------------------------------------------------------------------------

///|
pub fn face_var0(v : Int32) -> Face {
  FEq0(DVar(v))
}

///|
pub fn face_var1(v : Int32) -> Face {
  FEq1(DVar(v))
}

///|
pub fn face_eq0(r : Dim) -> Face {
  FEq0(r)
}

///|
pub fn face_eq1(r : Dim) -> Face {
  FEq1(r)
}

///|
pub fn face_and(a : Face, b : Face) -> Face {
  FAnd(a, b)
}

///|
pub fn face_or(a : Face, b : Face) -> Face {
  FOr(a, b)
}

///|
pub fn face_simplify(f : Face) -> Face {
  match f {
    FTop | FBot => f
    FEq0(r0) =>
      match dim_simplify(r0) {
        DZero => FTop
        DOne => FBot
        DNeg(x) => face_simplify(FEq1(x))
        DOr(a, b) =>
          face_simplify(FAnd(face_simplify(FEq0(a)), face_simplify(FEq0(b))))
        r => FEq0(r)
      }
    FEq1(r0) =>
      match dim_simplify(r0) {
        DZero => FBot
        DOne => FTop
        DNeg(x) => face_simplify(FEq0(x))
        DAnd(a, b) =>
          face_simplify(FAnd(face_simplify(FEq1(a)), face_simplify(FEq1(b))))
        r => FEq1(r)
      }
    FAnd(a0, b0) => {
      let a = face_simplify(a0)
      let b = face_simplify(b0)
      match (a, b) {
        (FBot, _) | (_, FBot) => FBot
        (FTop, x) | (x, FTop) => x
        _ => if a == b { a } else { FAnd(a, b) }
      }
    }
    FOr(a0, b0) => {
      let a = face_simplify(a0)
      let b = face_simplify(b0)
      match (a, b) {
        (FTop, _) | (_, FTop) => FTop
        (FBot, x) | (x, FBot) => x
        _ => if a == b { a } else { FOr(a, b) }
      }
    }
  }
}

///|
pub fn face_vars_into(f : Face, acc : Array[Int32]) -> Unit {
  match f {
    FTop | FBot => ()
    FEq0(r) | FEq1(r) => dim_vars_into(r, acc)
    FAnd(a, b) | FOr(a, b) => {
      face_vars_into(a, acc)
      face_vars_into(b, acc)
    }
  }
}

///|
pub fn face_vars(f : Face) -> Array[Int32] {
  let acc : Array[Int32] = []
  face_vars_into(f, acc)
  sort_ints(acc)
}

///|
pub fn face_nvars_sem(f : Face) -> Int32 {
  let vars = face_vars(f)
  let mut max_v = -1
  for v in vars {
    if v > max_v {
      max_v = v
    }
  }
  if max_v < 0 {
    0
  } else {
    max_v + 1
  }
}

///|
pub fn face_subst(f : Face, v : Int32, bit : Bool) -> Face {
  match f {
    FTop | FBot => f
    FEq0(r) => face_simplify(FEq0(dim_subst(r, v, bit)))
    FEq1(r) => face_simplify(FEq1(dim_subst(r, v, bit)))
    FAnd(a, b) =>
      face_simplify(FAnd(face_subst(a, v, bit), face_subst(b, v, bit)))
    FOr(a, b) =>
      face_simplify(FOr(face_subst(a, v, bit), face_subst(b, v, bit)))
  }
}

///|
pub fn bdd_of_face(f : Face, _nvars : Int32) -> Bdd {
  match f {
    FTop => BddOne
    FBot => BddZero
    FEq0(r) => bdd_not(bdd_of_dim(r))
    FEq1(r) => bdd_of_dim(r)
    FAnd(a, b) => bdd_and(bdd_of_face(a, _nvars), bdd_of_face(b, _nvars))
    FOr(a, b) => bdd_or(bdd_of_face(a, _nvars), bdd_of_face(b, _nvars))
  }
}

///|
fn eval_dim_bool(d : Dim, env : Array[Bool]) -> Bool {
  match d {
    DZero => false
    DOne => true
    DVar(i) => if i >= 0 && i < env.length() { env[i] } else { false }
    DNeg(a) => !eval_dim_bool(a, env)
    DAnd(a, b) => eval_dim_bool(a, env) && eval_dim_bool(b, env)
    DOr(a, b) => eval_dim_bool(a, env) || eval_dim_bool(b, env)
  }
}

///|
pub fn face_holds(f : Face, env : Array[Bool]) -> Bool {
  match f {
    FTop => true
    FBot => false
    FEq0(r) => !eval_dim_bool(r, env)
    FEq1(r) => eval_dim_bool(r, env)
    FAnd(a, b) => face_holds(a, env) && face_holds(b, env)
    FOr(a, b) => face_holds(a, env) || face_holds(b, env)
  }
}

///|
pub fn face_sat(f : Face, nvars : Int32) -> Bool {
  bdd_of_face(f, nvars) != BddZero
}

///|
pub fn face_witness(f : Face, nvars : Int32) -> Array[Bool]? {
  let b = bdd_of_face(f, nvars)
  if b == BddZero {
    return None
  }
  let out = Array::make(nvars, false)
  let mut cur = b
  while true {
    match cur {
      BddZero => return None
      BddOne => return Some(out)
      BddNode(v, lo, hi) =>
        if hi != BddZero {
          if v >= 0 && v < out.length() {
            out[v] = true
          }
          cur = hi
        } else {
          if v >= 0 && v < out.length() {
            out[v] = false
          }
          cur = lo
        }
    }
  }
  Some(out)
}

///|
pub fn face_is_bot_sem(f : Face) -> Bool {
  bdd_of_face(f, face_nvars_sem(f)) == BddZero
}

///|
pub fn face_is_top_sem(f : Face) -> Bool {
  bdd_of_face(f, face_nvars_sem(f)) == BddOne
}

///|
pub fn face_is_sat_sem(f : Face) -> Bool {
  !face_is_bot_sem(f)
}

///|
pub fn face_eq_mod(a : Face, b : Face, nvars : Int32) -> Bool {
  bdd_of_face(a, nvars) == bdd_of_face(b, nvars)
}

///|
pub fn bdd_face_eq(a : Face, b : Face, nvars : Int32) -> Bool {
  face_eq_mod(a, b, nvars)
}

///|
pub fn bdd_satisfying_cubes(b : Bdd, nvars : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  fn go(node : Bdd, cur : Array[Int32]) -> Unit {
    match node {
      BddZero => ()
      BddOne => out.push(cur.copy())
      BddNode(v, lo, hi) =>
        if v >= 0 && v < cur.length() {
          cur[v] = 0
          go(lo, cur)
          cur[v] = 1
          go(hi, cur)
          cur[v] = -1
        } else {
          go(lo, cur)
          go(hi, cur)
        }
    }
  }
  go(b, Array::make(nvars, -1))
  out
}
