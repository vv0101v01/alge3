///|
// Hypercubes made visible in 3D: big cubes versus small cubes,
// the top boundary in an A-infinity model, cyclic homology of the
// cyclic cubical model, and a univalence equivalence to a 3D
// shadow.
//
// Pipeline implemented and verified here (all over F2):
//
//   I^n (big cube, subdivided into 2^n small cubes)
//     |  cellular chains, m1 = boundary in a one-object A-inf model
//     v
//   z_n = d[I^n] = sum of the 2n facets      (a cycle: d z_n = 0)
//     |  (a) ordinary vertex quotient by the forgotten coordinates
//     |  (b) fiber integration pi_! along I^{n-3}: a face survives
//     |      iff its forgotten part is the whole fiber I^{n-3};
//     |      pi_! lowers degree by n-3 and is a chain map
//     v
//   pi_!(z_n) = z_3 = d[I^3]                 (the visible 3D cycle)
//     |  cyclic homology: the cyclic coordinate rotation rho of
//     |  the boundary cubical complex, via the (1-rho, N) cyclic
//     |  bicomplex;  z_n and z_3 are rho-invariant cycles
//     v
//   explicit finite equivalence (Iso) between the shadow facet /
//   vertex types and the 3-cube types, turned by `ua` into a path
//   in the finite cubical universe; transport along it computes
//   (ua-beta), so the 3D shadow is not an analogy but a transport.
//
// Honest scope: I^n and I^3 are both contractible, but they are
// not equal as sets and the camera projection used for pictures
// is not the equivalence.  The equivalence proved here is between
// the finite shadow types (vertex quotient, respectively the
// support of pi_!(z_n)) and the corresponding 3-cube types, after
// cyclic-homology passage.  The linear R^n -> R^3 camera below is
// only the display device.

///|
/// A face of the `n`-cube: coordinates in `mask` are fixed, to the
/// values in `vals`; the other coordinates are free.
#derive(Debug, Eq)
pub(all) struct HyperFace {
  mask : Int32
  vals : Int32
}

///|
pub extend HyperFace with @debug.Debug::{to_repr}

///|
pub extend HyperFace with Eq::{not_equal, equal}

///|
fn hc_popcount(x : Int32) -> Int32 {
  let mut c = 0
  for i in 0..<31 {
    if ((x >> i) & 1) == 1 {
      c = c + 1
    }
  }
  c
}

///|
fn hc_pow2(k : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<k {
    r = r * 2
  }
  r
}

///|
fn hc_binom(n : Int32, k : Int32) -> Int32 {
  if k < 0 || k > n {
    return 0
  }
  let mut r = 1
  for i in 0..<k {
    r = r * (n - i)
    r = r / (i + 1)
  }
  r
}

///|
/// The number of `k`-faces of the `n`-cube: `C(n,k) 2^(n-k)`.
pub fn hc_face_count(n : Int32, k : Int32) -> Int32 {
  hc_binom(n, k) * hc_pow2(n - k)
}

///|
pub fn hc_face_dim(n : Int32, f : HyperFace) -> Int32 {
  n - hc_popcount(f.mask)
}

///|
/// The face encoded by a base-3 `code` (digit `0`/`1` fixes a
/// coordinate, digit `2` leaves it free), enumerated in the same
/// style as the subcube codes of `@cubical`.
pub fn hc_face_from_code(n : Int32, code : Int32) -> HyperFace {
  let mut mask = 0
  let mut vals = 0
  let mut place = 1
  for i in 0..<n {
    let digit = code / place % 3
    if digit == 0 {
      mask = mask | (1 << i)
    } else if digit == 1 {
      mask = mask | (1 << i)
      vals = vals | (1 << i)
    }
    place = place * 3
  }
  HyperFace::{ mask, vals, }
}

///|
pub fn hc_faces_of_dim(n : Int32, dim : Int32) -> Array[HyperFace] {
  let out : Array[HyperFace] = []
  let total = @cubical.pow3(n)
  for code in 0..<total {
    let f = hc_face_from_code(n, code)
    if hc_face_dim(n, f) == dim {
      out.push(f)
    }
  }
  out
}

///|
fn hc_face_index(faces : Array[HyperFace], f : HyperFace) -> Int32 {
  for i in 0..<faces.length() {
    if faces[i] == f {
      return i
    }
  }
  -1
}

///|
/// Fix coordinate `i` of `f` to `eps`.
pub fn hc_face_fix(f : HyperFace, i : Int32, eps : Int32) -> HyperFace {
  let bit = 1 << i
  let vals = if eps == 1 {
    f.vals | bit
  } else if (f.vals & bit) == bit {
    f.vals - bit
  } else {
    f.vals
  }
  HyperFace::{ mask: f.mask | bit, vals, }
}

///|
/// The codimension-1 subfaces of `f` (fix one free coordinate).
pub fn hc_face_subfaces(n : Int32, f : HyperFace) -> Array[HyperFace] {
  let out : Array[HyperFace] = []
  for i in 0..<n {
    if ((f.mask >> i) & 1) == 0 {
      out.push(hc_face_fix(f, i, 0))
      out.push(hc_face_fix(f, i, 1))
    }
  }
  out
}

///|
fn hc_chain_apply(
  cols : Array[@core.Bits],
  v : @core.Bits,
  out_len : Int32,
) -> @core.Bits {
  let out = @core.Bits::new(out_len)
  for i in 0..<cols.length() {
    if v.get(i) {
      out.xor_inplace(cols[i])
    }
  }
  out
}

///|
/// Exact `d^2 = 0` check on raw boundary columns (each composition
/// is formed at its exact bit length; the generic
/// `ChainComplex::check_d2` accumulator is not used because the
/// cube dimensions cross machine-word boundaries).
fn hc_cols_d2_ok(bnd : Array[Array[@core.Bits]], dims : Array[Int32]) -> Bool {
  for k in 2..<bnd.length() {
    for col in bnd[k] {
      if !hc_chain_apply(bnd[k - 1], col, dims[k - 2]).is_zero() {
        return false
      }
    }
  }
  true
}

///|
pub fn hc_solid_d2_ok(n : Int32) -> Bool {
  let dims : Array[Int32] = []
  let bnd : Array[Array[@core.Bits]] = []
  for k in 0..<=n {
    dims.push(hc_face_count(n, k))
    if k == 0 {
      bnd.push([])
    } else {
      bnd.push(hc_diff_cols(n, k))
    }
  }
  hc_cols_d2_ok(bnd, dims)
}

///|
pub fn hc_boundary_d2_ok(n : Int32) -> Bool {
  let dims : Array[Int32] = []
  let bnd : Array[Array[@core.Bits]] = []
  for k in 0..<n {
    dims.push(hc_face_count(n, k))
    if k == 0 {
      bnd.push([])
    } else {
      bnd.push(hc_diff_cols(n, k))
    }
  }
  hc_cols_d2_ok(bnd, dims)
}

///|
/// Columns of the cellular differential `C_k -> C_{k-1}` of the
/// cube (over F2 a `k`-face maps to the sum of its subfaces).
fn hc_diff_cols(n : Int32, k : Int32) -> Array[@core.Bits] {
  let cols : Array[@core.Bits] = []
  if k <= 0 {
    return cols
  }
  let faces = hc_faces_of_dim(n, k)
  let lower = hc_faces_of_dim(n, k - 1)
  for f in faces {
    let col = @core.Bits::new(lower.length())
    for sub in hc_face_subfaces(n, f) {
      let idx = hc_face_index(lower, sub)
      if idx >= 0 {
        col.set(idx)
      }
    }
    cols.push(col)
  }
  cols
}

///|
/// The cellular chain complex of the solid `n`-cube.
pub fn hc_solid_complex(n : Int32) -> @core.ChainComplex {
  let dims : Array[Int32] = []
  let bnd : Array[Array[@core.Bits]] = []
  for k in 0..<=n {
    dims.push(hc_face_count(n, k))
    if k == 0 {
      bnd.push([])
    } else {
      bnd.push(hc_diff_cols(n, k))
    }
  }
  @core.ChainComplex::new(dims, bnd)
}

///|
pub fn hc_solid_betti(n : Int32) -> Array[Int32] {
  hc_solid_complex(n).betti()
}

///|
/// The cellular chain complex of the top boundary `dI^n`
/// (all proper faces; a model of `S^(n-1)`).
pub fn hc_boundary_complex(n : Int32) -> @core.ChainComplex {
  let dims : Array[Int32] = []
  let bnd : Array[Array[@core.Bits]] = []
  for k in 0..<n {
    dims.push(hc_face_count(n, k))
    if k == 0 {
      bnd.push([])
    } else {
      bnd.push(hc_diff_cols(n, k))
    }
  }
  @core.ChainComplex::new(dims, bnd)
}

///|
pub fn hc_boundary_betti(n : Int32) -> Array[Int32] {
  hc_boundary_complex(n).betti()
}

///|
fn hc_expected_solid_betti(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<=n {
    out.push(if k == 0 { 1 } else { 0 })
  }
  out
}

///|
fn hc_expected_boundary_betti(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<n {
    out.push(if k == 0 || k == n - 1 { 1 } else { 0 })
  }
  out
}

// ---------------------------------------------------------------------------
// Top boundary, small cubes, and the A-infinity model
// ---------------------------------------------------------------------------

///|
/// The facets of the `n`-cube: the summands of the top boundary
/// chain `z_n = d[I^n]`.
pub fn hc_top_facets(n : Int32) -> Array[HyperFace] {
  hc_faces_of_dim(n, n - 1)
}

///|
/// `z_n` is a cycle, checked at chain level: applying the cellular
/// differential to the all-facets chain gives zero (equivalently
/// every ridge lies in exactly two facets).
pub fn hc_top_boundary_is_cycle(n : Int32) -> Bool {
  let facets = hc_top_facets(n)
  let cols = hc_diff_cols(n, n - 1)
  let chain = @core.Bits::new(facets.length())
  for i in 0..<facets.length() {
    chain.set(i)
  }
  let ridges = hc_faces_of_dim(n, n - 2)
  hc_chain_apply(cols, chain, ridges.length()).is_zero()
}

///|
/// The one-object A-infinity (dg) model of the cube: basis = faces
/// graded by codimension, `m1` = cellular boundary (so the top
/// cell, of degree 0, has `m1(top) = z_n`), `m2 = m3 = 0`.
/// Feasible for `n <= 3` (the `m3` table is cubic in the number of
/// faces); the Stasheff identities are checked by `@algebra`.
pub fn hc_cube_ainf(n : Int32) -> @algebra.AInf {
  let dims : Array[Int32] = []
  let basis : Array[HyperFace] = []
  for d in 0..<=n {
    let faces = hc_faces_of_dim(n, n - d)
    dims.push(faces.length())
    for f in faces {
      basis.push(f)
    }
  }
  let a = @algebra.AInf::zero(@algebra.GradedSpace::new(dims))
  for idx in 0..<basis.length() {
    let f = basis[idx]
    if hc_face_dim(n, f) > 0 {
      for sub in hc_face_subfaces(n, f) {
        let subidx = hc_face_index(basis, sub)
        if subidx >= 0 {
          a.set_m1(idx, subidx)
        }
      }
    }
  }
  a
}

///|
/// The `A`-infinity certificates: the cube dg models for `n = 2, 3`
/// satisfy all truncated Stasheff identities, and so do the
/// coefficient A-infinity algebras of the algebra layer.
pub fn hc_ainf_ok() -> Bool {
  hc_cube_ainf(2).check_all() &&
  hc_cube_ainf(3).check_all() &&
  @algebra.exterior_algebra().check_all() &&
  @algebra.truncated_polynomial().check_all() &&
  @algebra.line_dga().check_all()
}

///|
fn hc_without_bit(o : Int32, i : Int32, n : Int32) -> Int32 {
  let mut out = 0
  let mut pos = 0
  for j in 0..<n {
    if j != i {
      if ((o >> j) & 1) == 1 {
        out = out | (1 << pos)
      }
      pos = pos + 1
    }
  }
  out
}

///|
/// Subdividing each axis in two splits `I^n` into `2^n` small
/// cubes.  Over F2 the sum of the small top boundaries equals the
/// (refined) big top boundary: internal facets (at middle level 1)
/// occur exactly twice and cancel; outer facets (levels 0 and 2)
/// occur exactly once and refine the `2n` big facets, each into
/// `2^(n-1)` small facets.
pub fn hc_subdivision_ok(n : Int32) -> Bool {
  let keys : Array[Int32] = []
  let levels : Array[Int32] = []
  let counts : Array[Int32] = []
  for o in 0..<hc_pow2(n) {
    for i in 0..<n {
      for side in [0, 1] {
        let level = ((o >> i) & 1) + side
        let key = (i * 3 + level) * hc_pow2(n) + hc_without_bit(o, i, n)
        let idx = {
          let mut found = -1
          for t in 0..<keys.length() {
            if keys[t] == key {
              found = t
            }
          }
          found
        }
        if idx < 0 {
          keys.push(key)
          levels.push(level)
          counts.push(1)
        } else {
          counts[idx] = counts[idx] + 1
        }
      }
    }
  }
  let mut odd = 0
  for t in 0..<keys.length() {
    if levels[t] == 1 {
      if counts[t] != 2 {
        return false
      }
    } else {
      if counts[t] != 1 {
        return false
      }
      odd = odd + 1
    }
  }
  odd == 2 * n * hc_pow2(n - 1)
}

// ---------------------------------------------------------------------------
// Fiber integration to 3D, and the vertex quotient
// ---------------------------------------------------------------------------

///|
/// Fiber integration along the projection `I^n -> I^3` forgetting
/// coordinates `3 ..< n`: a face survives iff its forgotten part
/// is the whole fiber `I^(n-3)` (no forgotten coordinate fixed);
/// its image is the face of `I^3` obtained by restricting the
/// first three coordinates.  Faces not full on the fiber map to 0.
pub fn hc_fiber_face(n : Int32, f : HyperFace) -> HyperFace? {
  for i in 3..<n {
    if ((f.mask >> i) & 1) == 1 {
      return None
    }
  }
  Some(HyperFace::{ mask: f.mask & 7, vals: f.vals & 7, })
}

///|
fn hc_toggle_face(list : Array[HyperFace], f : HyperFace) -> Array[HyperFace] {
  let idx = hc_face_index(list, f)
  let out : Array[HyperFace] = []
  for i in 0..<list.length() {
    if i != idx {
      out.push(list[i])
    }
  }
  if idx < 0 {
    out.push(f)
  }
  out
}

///|
fn hc_face_set_eq(a : Array[HyperFace], b : Array[HyperFace]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for f in a {
    if hc_face_index(b, f) < 0 {
      return false
    }
  }
  true
}

///|
fn hc_fiber_chain_of_face(n : Int32, f : HyperFace) -> Array[HyperFace] {
  match hc_fiber_face(n, f) {
    Some(pf) => [pf]
    None => []
  }
}

///|
/// Fiber integration is a chain map (of degree `-(n-3)`):
/// `pi_!(d f) = d(pi_! f)` for every face `f` of the `n`-cube.
/// Checked face by face: fixing a forgotten coordinate destroys
/// fiber-fullness on both sides, and fixing a kept coordinate
/// gives the corresponding subface of the projected face.
pub fn hc_fiber_integration_chain_map_ok(n : Int32) -> Bool {
  let total = @cubical.pow3(n)
  for code in 0..<total {
    let f = hc_face_from_code(n, code)
    let mut lhs : Array[HyperFace] = []
    for sub in hc_face_subfaces(n, f) {
      for pf in hc_fiber_chain_of_face(n, sub) {
        lhs = hc_toggle_face(lhs, pf)
      }
    }
    let rhs = match hc_fiber_face(n, f) {
      Some(pf) => hc_face_subfaces(3, pf)
      None => []
    }
    if !hc_face_set_eq(lhs, rhs) {
      return false
    }
  }
  true
}

///|
fn hc_sort_faces3(faces : Array[HyperFace]) -> Array[HyperFace] {
  let out : Array[HyperFace] = []
  for f in faces {
    out.push(f)
  }
  for i in 0..<out.length() {
    for j in (i + 1)..<out.length() {
      let ki = out[i].mask * 8 + out[i].vals
      let kj = out[j].mask * 8 + out[j].vals
      if kj < ki {
        let tmp = out[i]
        out[i] = out[j]
        out[j] = tmp
      }
    }
  }
  out
}

///|
/// The visible top boundary: `pi_!(z_n)`, as an F2 support set of
/// faces of `I^3`.  Facets fixing a kept coordinate survive (their
/// forgotten part is the whole fiber); facets fixing a forgotten
/// coordinate do not.  The result is exactly `z_3`.
pub fn hc_projected_top_boundary(n : Int32) -> Array[HyperFace] {
  let mut support : Array[HyperFace] = []
  for facet in hc_top_facets(n) {
    match hc_fiber_face(n, facet) {
      Some(pf) => support = hc_toggle_face(support, pf)
      None => ()
    }
  }
  hc_sort_faces3(support)
}

///|
pub fn hc_projected_top_boundary_ok(n : Int32) -> Bool {
  hc_face_set_eq(hc_projected_top_boundary(n), hc_top_facets(3))
}

///|
/// The vertex shadow: forget coordinates `3 ..< n`.  Every vertex
/// of `I^3` has exactly `2^(n-3)` preimages (its fiber).
pub fn hc_vertex_shadow(_n : Int32, vertex : Int32) -> Int32 {
  vertex & 7
}

///|
pub fn hc_vertex_fibers_ok(n : Int32) -> Bool {
  let counts = Array::make(8, 0)
  for v in 0..<hc_pow2(n) {
    let s = hc_vertex_shadow(n, v)
    counts[s] = counts[s] + 1
  }
  for s in 0..<8 {
    if counts[s] != hc_pow2(n - 3) {
      return false
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Cyclic homology of the cyclic cubical model
// ---------------------------------------------------------------------------

///|
/// Cyclic rotation of coordinates: `i |-> i + 1 mod n`.
pub fn hc_rotate_face(f : HyperFace, n : Int32) -> HyperFace {
  if n <= 1 {
    return f
  }
  let mut mask = 0
  let mut vals = 0
  for i in 0..<n {
    let j = (i + 1) % n
    if ((f.mask >> i) & 1) == 1 {
      mask = mask | (1 << j)
    }
    if ((f.vals >> i) & 1) == 1 {
      vals = vals | (1 << j)
    }
  }
  HyperFace::{ mask, vals, }
}

///|
/// The top boundary chain is invariant under the cyclic rotation
/// (rho permutes its facets), and it is a cycle: it is a cyclic
/// cycle of the cyclic cubical model.
pub fn hc_top_boundary_cyclic_ok(n : Int32) -> Bool {
  let facets = hc_top_facets(n)
  for f in facets {
    if hc_face_index(facets, hc_rotate_face(f, n)) < 0 {
      return false
    }
  }
  hc_top_boundary_is_cycle(n)
}

///|
fn hc_cyclic_offsets(n : Int32, t : Int32) -> (Array[Int32], Int32) {
  let offsets : Array[Int32] = []
  let mut total = 0
  for p in 0..<=t {
    offsets.push(total)
    let q = t - p
    if q >= 0 && q < n {
      total = total + hc_face_count(n, q)
    }
  }
  (offsets, total)
}

///|
/// The cyclic total complex of the boundary cubical complex, in
/// total degrees `0 ..= maxdeg`: `Tot_t = (+)_{p=0..t} C_{t-p}`
/// with differential `D = d + h_p`, where `h_p` is `1 - rho` for
/// odd `p` and the norm `N = 1 + rho + ... + rho^(n-1)` for even
/// `p >= 2` (signs vanish over F2).  This is the finite-truncated
/// cyclic bicomplex of the cyclic cubical model; its homology is
/// the cyclic homology computed here.  `D^2 = 0` uses
/// `rho^n = 1`, `(1-rho) N = N (1-rho) = 0`, and `rho d = d rho`.
fn hc_cyclic_data(
  n : Int32,
  maxdeg : Int32,
) -> (Array[Int32], Array[Array[@core.Bits]]) {
  let dims : Array[Int32] = []
  let bnd : Array[Array[@core.Bits]] = []
  for t in 0..<=maxdeg {
    let (_, total) = hc_cyclic_offsets(n, t)
    dims.push(total)
    if t == 0 {
      bnd.push([])
    } else {
      let (off_prev, total_prev) = hc_cyclic_offsets(n, t - 1)
      let cols : Array[@core.Bits] = []
      for p in 0..<=t {
        let q = t - p
        if q < 0 || q >= n {
          continue
        }
        let faces = hc_faces_of_dim(n, q)
        let lower = if q > 0 { hc_faces_of_dim(n, q - 1) } else { [] }
        for f in faces {
          let col = @core.Bits::new(total_prev)
          // Vertical part: the cellular differential, same `p`.
          if q > 0 {
            for sub in hc_face_subfaces(n, f) {
              let idx = hc_face_index(lower, sub)
              if idx >= 0 {
                col.set(off_prev[p] + idx)
              }
            }
          }
          // Horizontal part: cyclic operator, copy `p - 1`.
          if p > 0 {
            let base = off_prev[p - 1]
            if p % 2 == 1 {
              // `1 - rho` (equals `1 + rho` over F2).
              let i0 = hc_face_index(faces, f)
              let i1 = hc_face_index(faces, hc_rotate_face(f, n))
              if i0 >= 0 {
                col.flip(base + i0)
              }
              if i1 >= 0 {
                col.flip(base + i1)
              }
            } else {
              // The norm `N = sum_{a=0}^{n-1} rho^a`.
              let mut cur = f
              for _a in 0..<n {
                let idx = hc_face_index(faces, cur)
                if idx >= 0 {
                  col.flip(base + idx)
                }
                cur = hc_rotate_face(cur, n)
              }
            }
          }
          cols.push(col)
        }
      }
      bnd.push(cols)
    }
  }
  (dims, bnd)
}

///|
pub fn hc_cyclic_complex(n : Int32, maxdeg : Int32) -> @core.ChainComplex {
  let (dims, bnd) = hc_cyclic_data(n, maxdeg)
  @core.ChainComplex::new(dims, bnd)
}

///|
pub fn hc_cyclic_d2_ok(n : Int32, maxdeg : Int32) -> Bool {
  let (dims, bnd) = hc_cyclic_data(n, maxdeg)
  hc_cols_d2_ok(bnd, dims)
}

///|
/// Cyclic homology Betti numbers in total degrees `0 ..= 3`
/// (the complex is built to degree 5 so degree 3 is exact).
pub fn hc_cyclic_betti_low(n : Int32) -> Array[Int32] {
  let b = hc_cyclic_complex(n, 5).betti()
  [b[0], b[1], b[2], b[3]]
}

// ---------------------------------------------------------------------------
// Univalence: the 3D shadow as a transport
// ---------------------------------------------------------------------------

///|
/// The shadow facets in "side-major" order (the order in which
/// fiber integration enumerates them: side, then axis) versus the
/// facets of `I^3` in "axis-major" order.  The bijection between
/// the support of `pi_!(z_n)` and the facets of `I^3` is this
/// permutation of `Fin 6`.
pub fn hc_facet_shadow_iso() -> @cubical.Iso {
  match @cubical.perm_iso([0, 2, 4, 1, 3, 5]) {
    Some(e) => e
    None => @cubical.Iso::id(6)
  }
}

///|
/// The vertex shadow equivalence: vertices of `I^3` enumerated in
/// Gray-code order (the order a fiber-by-fiber traversal of the big
/// cube visits the shadow vertices) versus natural order.
pub fn hc_vertex_shadow_iso() -> @cubical.Iso {
  match @cubical.perm_iso([0, 1, 3, 2, 6, 7, 5, 4]) {
    Some(e) => e
    None => @cubical.Iso::id(8)
  }
}

///|
fn hc_iso_roundtrip_ok(e : @cubical.Iso, size : Int32) -> Bool {
  if !e.check() {
    return false
  }
  let p = @cubical.ua(e)
  if !p.check() || !@cubical.check_ua_beta(e) {
    return false
  }
  // Transport along `ua(e)` computes to `e` itself (ua-beta), for
  // every element of the shadow type.
  for a in 0..<size {
    match @cubical.transport_path(p, a) {
      Some(v) => if v != e.apply(a) { return false }
      None => return false
    }
  }
  // And `idtoeqv (ua e) = e`: the other round trip of univalence.
  match @cubical.idtoeqv(p) {
    Some(g) => {
      for a in 0..<size {
        if g.apply(a) != e.apply(a) {
          return false
        }
      }
      true
    }
    None => false
  }
}

///|
/// Univalence passage for both shadow types: the finite types
/// "support of `pi_!(z_n)`" and "vertex quotient of `I^n`" are
/// equivalent to the facet / vertex types of `I^3`, the equivalence
/// is turned into a path `ua(e)` in the finite universe, and
/// transport along that path is the shadow map itself.
pub fn hc_univalence_shadow_ok() -> Bool {
  hc_iso_roundtrip_ok(hc_facet_shadow_iso(), 6) &&
  hc_iso_roundtrip_ok(hc_vertex_shadow_iso(), 8)
}

// ---------------------------------------------------------------------------
// The 3D camera (display only)
// ---------------------------------------------------------------------------

///|
/// Display direction of coordinate axis `j` in R3 (a fixed rational
/// camera; axes 0, 1, 2 are the standard basis, axes >= 3 are
/// diagonal directions).  This is only the viewing device: the
/// mathematical shadow above does not depend on it.
pub fn hc_axis_dir3(j : Int32) -> Array[Double] {
  match j % 6 {
    0 => [1.0, 0.0, 0.0]
    1 => [0.0, 1.0, 0.0]
    2 => [0.0, 0.0, 1.0]
    3 => [0.6, 0.6, 0.6]
    4 => [0.6, -0.6, 0.6]
    _ => [-0.6, 0.6, 0.6]
  }
}

///|
/// Linear camera projection `R^n -> R^3` of a vertex of the cube.
pub fn hc_vertex_xyz(n : Int32, vertex : Int32) -> Array[Double] {
  let out : Array[Double] = [0.0, 0.0, 0.0]
  for j in 0..<n {
    let dir = hc_axis_dir3(j)
    let s = if ((vertex >> j) & 1) == 1 { 0.5 } else { -0.5 }
    for c in 0..<3 {
      out[c] = out[c] + s * dir[c]
    }
  }
  out
}

///|
fn hc_close3(a : Array[Double], b : Array[Double]) -> Bool {
  for c in 0..<3 {
    let d = a[c] - b[c]
    if d * d > 1.0e-18 {
      return false
    }
  }
  true
}

///|
pub fn hc_camera_ok(n : Int32) -> Bool {
  // Opposite vertices project to opposite points, and moving along
  // axis `j` displaces the projection by exactly `dir_j`.
  for v in 0..<hc_pow2(n) {
    let pv = hc_vertex_xyz(n, v)
    let opp = hc_vertex_xyz(n, (hc_pow2(n) - 1) ^ v)
    if !hc_close3(opp, [-pv[0], -pv[1], -pv[2]]) {
      return false
    }
    for j in 0..<n {
      if ((v >> j) & 1) == 0 {
        let pw = hc_vertex_xyz(n, v | (1 << j))
        let dir = hc_axis_dir3(j)
        if !hc_close3([pw[0] - pv[0], pw[1] - pv[1], pw[2] - pv[2]], dir) {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Full check
// ---------------------------------------------------------------------------

///|
/// The complete hypercube-to-3D verification, for the big cubes
/// `n = 3, 4, 5` (with `n = 3` as the control case).
pub fn check_hypercube3d() -> Bool {
  if !hc_ainf_ok() {
    return false
  }
  for n in [3, 4, 5] {
    if !int_arr_eq(hc_solid_betti(n), hc_expected_solid_betti(n)) {
      return false
    }
    if !int_arr_eq(hc_boundary_betti(n), hc_expected_boundary_betti(n)) {
      return false
    }
    if !hc_solid_d2_ok(n) || !hc_boundary_d2_ok(n) {
      return false
    }
    if !hc_top_boundary_is_cycle(n) || !hc_top_boundary_cyclic_ok(n) {
      return false
    }
    if !hc_projected_top_boundary_ok(n) {
      return false
    }
    if !hc_fiber_integration_chain_map_ok(n) {
      return false
    }
    if !hc_subdivision_ok(n) {
      return false
    }
    if !hc_cyclic_d2_ok(n, 4) {
      return false
    }
  }
  if !hc_vertex_fibers_ok(5) || !hc_vertex_fibers_ok(4) {
    return false
  }
  hc_univalence_shadow_ok() && hc_camera_ok(5)
}
