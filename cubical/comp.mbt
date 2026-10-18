///|
/// A partial element (system) of a cubical type: components on subcubes
/// inside the extent of `phi`, pairwise compatible on overlaps.  This is
/// the data of an element of `Partial phi A`, and the "tube" of an open
/// box for `comp`.
pub struct PartialElem {
  phi : Cof
  comps : Array[Int32]
  vals : Array[Int32]
}

///|
pub fn PartialElem::new(
  phi : Cof,
  comps : Array[Int32],
  vals : Array[Int32],
) -> PartialElem {
  PartialElem::{ phi, comps, vals, }
}

///|
/// The empty partial element, defined on `⊥`.
pub fn partial_empty() -> PartialElem {
  PartialElem::{ phi: CBot, comps: [], vals: [], }
}

///|
/// Compatibility of a system: every component lives on a subcube in the
/// extent of `phi`, takes values in range, and any two components agree
/// on the intersection of their subcubes.
pub fn check_partial(x : CubeTy, p : PartialElem) -> Bool {
  let n = x.n
  if p.comps.length() != p.vals.length() {
    return false
  }
  for k in 0..<p.comps.length() {
    let s = p.comps[k]
    if !p.phi.holds_code(s, n) || p.vals[k] < 0 || p.vals[k] >= x.card[s] {
      return false
    }
  }
  for i in 0..<p.comps.length() {
    for j in 0..<p.comps.length() {
      let m = meet_cube(p.comps[i], p.comps[j], n)
      if m >= 0 &&
        x.restrict(p.comps[i], m, p.vals[i]) !=
        x.restrict(p.comps[j], m, p.vals[j]) {
        return false
      }
    }
  }
  true
}

///|
/// The value of a partial element at a subcube, if covered by some
/// component.  Compatibility guarantees the value is independent of the
/// chosen component.
pub fn partial_value_at(x : CubeTy, p : PartialElem, stage : Int32) -> Int32? {
  for k in 0..<p.comps.length() {
    if is_subface(stage, p.comps[k], x.n) {
      return Some(x.restrict(p.comps[k], stage, p.vals[k]))
    }
  }
  None
}

///|
/// The result of a Kan composition: the lid (the value of `comp`), one
/// chosen filler cube (the value of `fill`, an element over the generic
/// subcube), how many fillers exist, and whether the lid is independent
/// of the choice of filler.
pub struct CompResult {
  lid : Int32
  filler : Int32
  fillers : Int32
  unique_lid : Bool
}

///|
/// Heterogeneous composition along coordinate `dir`:
///
/// ```text
/// comp^i A [phi ↦ u] u0 : A(1)
/// ```
///
/// where `x` is the line of types `A` over the ambient cube (with `dir`
/// the composition direction), `tube` is a partial element whose
/// components live on subcubes with `dir` free (the sides of the box), and
/// `cap` is an element over the `dir = 0` face agreeing with the tube
/// there.  The algorithm is finite Kan filling: enumerate the finitely
/// many cubes over the generic subcube, keep those restricting to the cap
/// and to every tube component, and read off the `dir = 1` face.  Returns
/// `None` exactly when the box has no filler (ill-formed box: the sides
/// and cap are incompatible).  Cost: `O(|A_generic| · (1 + #tube))`
/// restriction lookups.
pub fn comp(
  x : CubeTy,
  dir : Int32,
  tube : PartialElem,
  cap : Int32,
) -> CompResult? {
  let n = x.n
  let gen = generic_cube(n)
  let cap_stage = face_cube(n, dir, 0)
  let lid_stage = face_cube(n, dir, 1)
  if cap < 0 || cap >= x.card[cap_stage] {
    return None
  }
  let mut chosen = -1
  let mut count = 0
  let mut lid0 = -1
  let mut unique = true
  for cand in 0..<x.card[gen] {
    let mut ok = x.restrict(gen, cap_stage, cand) == cap
    for k in 0..<tube.comps.length() {
      if x.restrict(gen, tube.comps[k], cand) != tube.vals[k] {
        ok = false
      }
    }
    if ok {
      count = count + 1
      let lid = x.restrict(gen, lid_stage, cand)
      if chosen < 0 {
        chosen = cand
        lid0 = lid
      } else if lid != lid0 {
        unique = false
      }
    }
  }
  if chosen < 0 {
    None
  } else {
    Some(CompResult::{
      lid: lid0,
      filler: chosen,
      fillers: count,
      unique_lid: unique,
    })
  }
}

///|
/// Homogeneous composition in a fixed type `x` over the remaining
/// dimensions: extend `x` constantly along a fresh composition direction
/// and apply `comp`.  Path composition is the special case where the tube
/// has two components.
pub fn hcomp(x : CubeTy, tube : PartialElem, cap : Int32) -> CompResult? {
  comp(extend_ty(x), x.n, tube, cap)
}

///|
/// Transport along a line of types: `comp` with the empty tube.
/// `transp_line x dir a : x(dir=1)` for `a : x(dir=0)` (elements coded at
/// the respective faces, other coordinates free).
pub fn transp_line(x : CubeTy, dir : Int32, a : Int32) -> Int32? {
  match comp(x, dir, partial_empty(), a) {
    Some(r) => Some(r.lid)
    None => None
  }
}

///|
/// The filler of a transport: a line (element over the generic subcube)
/// from `a` to `transp_line x dir a`.  Its two faces are the endpoints.
pub fn fill_line(x : CubeTy, dir : Int32, a : Int32) -> Int32? {
  match comp(x, dir, partial_empty(), a) {
    Some(r) => Some(r.filler)
    None => None
  }
}

///|
/// The isomorphism between the two end faces of a line of types, read off
/// at a fixed stage of the remaining dimensions.  `mid_stage` is a subcube
/// with coordinate `dir` free; the result is the transport isomorphism
/// between its `dir = 0` and `dir = 1` faces, given by
/// `res(mid→1) ∘ res(mid→0)^{-1}`.  `None` iff some restriction is not a
/// bijection (the line is not an equivalence of finite types).
pub fn stage_line_iso(x : CubeTy, mid_stage : Int32, dir : Int32) -> Iso? {
  let s0 = subcube_set_digit(mid_stage, dir, 0)
  let s1 = subcube_set_digit(mid_stage, dir, 1)
  let r0 = x.res_fn(mid_stage, s0)
  let r1 = x.res_fn(mid_stage, s1)
  match (fn_inv(r0, x.card[s0]), fn_inv(r1, x.card[s1])) {
    (Some(i0), Some(i1)) =>
      Some(Iso::{
        dom: x.card[s0],
        cod: x.card[s1],
        fwd: fn_comp(i0, r1),
        bwd: fn_comp(i1, r0),
      })
    _ => None
  }
}

///|
/// The `unglue` eliminator at a stage: an element of
/// `Glue [phi ↦ (T, e)] A` at stage `sigma`, mapped into `A`.  On the
/// extent of `phi` this is `e[sigma]` (the strict computation rule
/// `unglue (glue [phi ↦ t] a) = a` and, when `phi` holds, `unglue g = e g`).
pub fn unglue_at(
  phi : Cof,
  t : CubeTy,
  a : CubeTy,
  e : Array[Array[Int32]],
  sigma : Int32,
  x : Int32,
) -> Int32 {
  ignore(t)
  ignore(a)
  if phi.holds_code(sigma, a.n) {
    e[sigma][x]
  } else {
    x
  }
}

///|
/// The `glue` constructor at a stage: from a partial element `u` of `T` on
/// `phi` and a value `b` of `A` at `sigma` with `e(u) = b` wherever `u` is
/// defined, build an element of the Glue type at `sigma`.  When `phi`
/// holds at `sigma` the result is `u|sigma` (strictly); otherwise it is
/// `b`.  Returns `None` if the compatibility `e(u) = b` fails.
pub fn glue_at(
  phi : Cof,
  t : CubeTy,
  a : CubeTy,
  e : Array[Array[Int32]],
  sigma : Int32,
  u : PartialElem,
  b : Int32,
) -> Int32? {
  if phi.holds_code(sigma, a.n) {
    match partial_value_at(t, u, sigma) {
      Some(tv) => if e[sigma][tv] == b { Some(tv) } else { None }
      None => None
    }
  } else {
    // compatibility still has to hold on every face of sigma in the extent
    let n = a.n
    let mut ok = true
    for face in 0..<pow3(n) {
      if is_subface(face, sigma, n) && phi.holds_code(face, n) {
        match partial_value_at(t, u, face) {
          Some(tv) =>
            if e[face][tv] != a.restrict(sigma, face, b) {
              ok = false
            }
          None => ok = false
        }
      }
    }
    if ok {
      Some(b)
    } else {
      None
    }
  }
}
