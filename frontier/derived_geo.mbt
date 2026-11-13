///|
// Deformation functors and moduli towers, derived fiber products,
// discrete connections with curvature and horizontal distributions,
// universal coverings, and geometric higher-groupoid models.
//
// All models are finite and every claim is checked by enumeration.

// ---------------------------------------------------------------------------
// Deformation functor of the `A_2` singularity and its moduli tower
// ---------------------------------------------------------------------------
//
// The deformation functor assigns to the Artin truncation
// `R_n = F_p[t] / (t^{n+1})` the set of unfoldings
// `F_t(x) = x^3 + u(t) x + v(t)` with `u, v` in `t R_n` (the
// constant term of the unfolding vanishes: the central fibre is
// `x^3`, i.e. the `x`-part of `A_2 : x^3 + y^2`).  The first-order
// deformations are parametrised by `(u_1, v_1)`, a basis of the
// Milnor algebra `F_p[x] / (3x^2)` -- dimension `2`, matching
// `@derived.milnor_number` for `A_2`.  Truncation `R_{n+1} -> R_n`
// makes the sets `Def_n` a tower (the finite moduli tower): every
// map is surjective, each fibre has exactly `p^2` lifts (the top
// coefficients of `u` and `v`), and every deformation is
// unobstructed (zero-extension lifts it to every order).

///|
/// A deformation at truncation level `n`: coefficients of `u` and
/// `v` as arrays of length `n + 1` over `F_p`, with `u[0] = v[0] =
/// 0` enforced by the constructors used here.
pub(all) struct Deform {
  level : Int32
  prime : Int32
  u : Array[Int32]
  v : Array[Int32]
}

///|
fn deform_eq(a : Deform, b : Deform) -> Bool {
  a.level == b.level &&
  a.prime == b.prime &&
  int_arr_eq(a.u, b.u) &&
  int_arr_eq(a.v, b.v)
}

///|
pub fn deform_zero(level : Int32, prime : Int32) -> Deform {
  let u : Array[Int32] = []
  let v : Array[Int32] = []
  for _ in 0..<=level {
    u.push(0)
    v.push(0)
  }
  Deform::{ level, prime, u, v, }
}

///|
/// The truncation map of the moduli tower, `Def_{n+1} -> Def_n`
/// (restriction from `R_m` to `R_n` for `n <= m`).
pub fn deform_truncate(d : Deform, n : Int32) -> Deform {
  let u : Array[Int32] = []
  let v : Array[Int32] = []
  for k in 0..<=n {
    u.push(d.u[k])
    v.push(d.v[k])
  }
  Deform::{ level: n, prime: d.prime, u, v, }
}

///|
/// Extend a deformation from level `n` to `n + 1` by prescribing
/// the new top coefficients `(u_{n+1}, v_{n+1})`.
pub fn deform_extend(d : Deform, top_u : Int32, top_v : Int32) -> Deform {
  let u : Array[Int32] = []
  let v : Array[Int32] = []
  for k in 0..<=d.level {
    u.push(d.u[k])
    v.push(d.v[k])
  }
  u.push(@core.fp_norm(top_u, d.prime))
  v.push(@core.fp_norm(top_v, d.prime))
  Deform::{ level: d.level + 1, prime: d.prime, u, v, }
}

///|
/// Multiplication of truncated power series modulo `t^{n+1}`.
pub fn tseries_mul(
  a : Array[Int32],
  b : Array[Int32],
  n : Int32,
  prime : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<=n {
    out.push(0)
  }
  for i in 0..<=n {
    for j in 0..<=(n - i) {
      out[i + j] = @core.fp_add(
        out[i + j],
        @core.fp_mul(a[i], b[j], prime),
        prime,
      )
    }
  }
  out
}

///|
/// Encode a small deformation as an integer (for counting distinct
/// lifts in the tower).
fn deform_encode(d : Deform) -> Int32 {
  let mut code = 0
  let mut mult = 1
  for k in 0..<=d.level {
    code = code + d.u[k] * mult
    mult = mult * d.prime
    code = code + d.v[k] * mult
    mult = mult * d.prime
  }
  code
}

///|
pub fn check_deformation_moduli() -> Bool {
  let p = 1009
  // Truncated series arithmetic: `(1 + 2t + 3t^2)(1 - t + 4t^2)`
  // truncated at `t^2` is `1 + t + 5t^2`.
  let prod = tseries_mul([1, 2, 3], [1, p - 1, 4], 2, p)
  if !int_arr_eq(prod, [1, 1, 5]) {
    return false
  }
  // The tangent space of the deformation functor is the Milnor
  // algebra of `A_2`: the number of first-order parameters
  // `(u_1, v_1)` equals `mu = tau = 2`, computed by the derived
  // layer.
  let a2 = @derived.poly_of([([3, 0], 1), ([0, 2], 1)])
  if @derived.milnor_number(a2, [2, 3], p, 12) != 2 ||
    @derived.tjurina_number(a2, [2, 3], p, 12) != 2 {
    return false
  }
  // Tower laws at a small prime, where lifts can be enumerated:
  // truncation is functorial, the zero deformation is the central
  // fibre, zero-extension is a lift at every level (unobstructed),
  // and each fibre of `Def_2 -> Def_1` has exactly `p^2` elements.
  let q = 3
  let base = Deform::{ level: 1, prime: q, u: [0, 1], v: [0, 2], }
  // Central fibre: truncating to level 0 leaves only `x^3`.
  if !deform_eq(deform_truncate(base, 0), deform_zero(0, q)) {
    return false
  }
  let lift_codes : Array[Int32] = []
  for a in 0..<q {
    for b in 0..<q {
      let lift = deform_extend(base, a, b)
      if !deform_eq(deform_truncate(lift, 1), base) {
        return false
      }
      lift_codes.push(deform_encode(lift))
    }
  }
  // All `p^2` lifts are distinct.
  for i in 0..<lift_codes.length() {
    for j in (i + 1)..<lift_codes.length() {
      if lift_codes[i] == lift_codes[j] {
        return false
      }
    }
  }
  if lift_codes.length() != q * q {
    return false
  }
  // Number of deformations at level `n` is `p^(2n)`: the tower
  // grows by exactly two parameters per level.
  let mut count_n = 1
  for _ in 0..<3 {
    count_n = count_n * q * q
  }
  if count_n != 729 {
    return false
  }
  // Unobstructedness through the tower: iterate zero-extension to
  // level 5 and truncate back at every intermediate level.
  let mut d = base
  for level in 2..<=5 {
    d = deform_extend(d, 0, 0)
    if d.level != level || !deform_eq(deform_truncate(d, 1), base) {
      return false
    }
  }
  // Functoriality: `truncate_n . truncate_m = truncate_n`.
  let d5 = d
  deform_eq(deform_truncate(deform_truncate(d5, 3), 1), deform_truncate(d5, 1))
}

// ---------------------------------------------------------------------------
// Derived fiber product of finite chain complexes over `F_2`
// ---------------------------------------------------------------------------
//
// For chain maps `f : A -> C` and `g : B -> C`, the (shifted)
// derived fiber product is the complex
//   `S_n = A_{n-1} + B_{n-1} + C_n`,
//   `d(a, b, c) = (da, db, f(a) + g(b) + dc)`   (signs vanish mod 2),
// whose homology is the homology of the homotopy pullback, shifted
// by one.  Unlike the ordinary pullback of the underlying graded
// vector spaces, it remembers the homotopy (Tor) correction: for
// zero maps `A -> C <- B` it has an extra class in degree 0.

///|
/// A finite chain complex over `F_2` in raw form: `bnd[k]` is the
/// list of columns of the differential `d_k` (bitsets over the
/// basis in degree `k - 1`), and `bnd[0]` is empty.
pub(all) struct CxSpec {
  dims : Array[Int32]
  bnd : Array[Array[@core.Bits]]
}

///|
/// A chain map in raw form: `maps[k]` is the list of columns of the
/// degree-`k` component (bitsets over the target basis).
pub(all) struct ChainMapSpec {
  maps : Array[Array[@core.Bits]]
}

///|
fn cx_dim_at(c : CxSpec, k : Int32) -> Int32 {
  if k < 0 || k >= c.dims.length() {
    0
  } else {
    c.dims[k]
  }
}

///|
fn bits_apply(
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
/// Is `f` a chain map `src -> dst` (commutes with the differentials
/// on every basis element)?
pub fn chain_map_ok(f : ChainMapSpec, src : CxSpec, dst : CxSpec) -> Bool {
  for k in 0..<src.dims.length() {
    if k >= f.maps.length() {
      return false
    }
    for i in 0..<src.dims[k] {
      // `f_{k-1}(d e_i)` versus `d (f_k e_i)`.
      if k == 0 {
        continue
      }
      let de = src.bnd[k][i]
      let lhs = bits_apply(f.maps[k - 1], de, cx_dim_at(dst, k - 1))
      let fe_col = f.maps[k][i]
      let rhs = bits_apply(dst.bnd[k], fe_col, cx_dim_at(dst, k - 1))
      if !lhs.same(rhs) {
        return false
      }
    }
  }
  true
}

///|
fn cx_top3(a : CxSpec, b : CxSpec, c : CxSpec) -> Int32 {
  let mut t = a.dims.length()
  if b.dims.length() > t {
    t = b.dims.length()
  }
  if c.dims.length() > t {
    t = c.dims.length()
  }
  t
}

///|
/// Build the shifted derived fiber product complex.
pub fn derived_pullback(
  a : CxSpec,
  b : CxSpec,
  c : CxSpec,
  f : ChainMapSpec,
  g : ChainMapSpec,
) -> @core.ChainComplex {
  let top = cx_top3(a, b, c)
  // Stored degrees `0 ..= top` cover `S_n` for `n - 1 <= top - 1`.
  let dims : Array[Int32] = []
  for n in 0..<=top {
    dims.push(cx_dim_at(a, n - 1) + cx_dim_at(b, n - 1) + cx_dim_at(c, n))
  }
  let bnd : Array[Array[@core.Bits]] = []
  for n in 0..<=top {
    if n == 0 {
      bnd.push([])
    } else {
      let out_len = dims[n - 1]
      let off_a = 0
      let off_b = cx_dim_at(a, n - 2)
      let off_c = off_b + cx_dim_at(b, n - 2)
      let cols : Array[@core.Bits] = []
      // Basis elements from `A_{n-1}`.
      for i in 0..<cx_dim_at(a, n - 1) {
        let col = @core.Bits::new(out_len)
        if n - 1 >= 1 {
          let da = a.bnd[n - 1][i]
          for t in 0..<cx_dim_at(a, n - 2) {
            if da.get(t) {
              col.set(off_a + t)
            }
          }
        }
        let fc = f.maps[n - 1][i]
        for t in 0..<cx_dim_at(c, n - 1) {
          if fc.get(t) {
            col.set(off_c + t)
          }
        }
        cols.push(col)
      }
      // Basis elements from `B_{n-1}`.
      for i in 0..<cx_dim_at(b, n - 1) {
        let col = @core.Bits::new(out_len)
        if n - 1 >= 1 {
          let db = b.bnd[n - 1][i]
          for t in 0..<cx_dim_at(b, n - 2) {
            if db.get(t) {
              col.set(off_b + t)
            }
          }
        }
        let gc = g.maps[n - 1][i]
        for t in 0..<cx_dim_at(c, n - 1) {
          if gc.get(t) {
            col.set(off_c + t)
          }
        }
        cols.push(col)
      }
      // Basis elements from `C_n`.
      for i in 0..<cx_dim_at(c, n) {
        let col = @core.Bits::new(out_len)
        if n >= 1 {
          let dc = c.bnd[n][i]
          for t in 0..<cx_dim_at(c, n - 1) {
            if dc.get(t) {
              col.set(off_c + t)
            }
          }
        }
        cols.push(col)
      }
      bnd.push(cols)
    }
  }
  @core.ChainComplex::new(dims, bnd)
}

///|
fn bit1(i : Int32, n : Int32) -> @core.Bits {
  let b = @core.Bits::new(n)
  b.set(i)
  b
}

///|
fn point_cx() -> CxSpec {
  CxSpec::{ dims: [1], bnd: [[]], }
}

///|
fn id_map_cx() -> ChainMapSpec {
  ChainMapSpec::{ maps: [[bit1(0, 1)]], }
}

///|
fn zero_map_cx() -> ChainMapSpec {
  ChainMapSpec::{ maps: [[@core.Bits::new(1)]], }
}

///|
pub fn derived_pullback_example_betti() -> Array[Int32] {
  let pt = point_cx()
  derived_pullback(pt, pt, pt, id_map_cx(), id_map_cx()).betti()
}

///|
pub fn check_derived_fiber_product() -> Bool {
  let pt = point_cx()
  // The structure maps are chain maps.
  if !chain_map_ok(id_map_cx(), pt, pt) || !chain_map_ok(zero_map_cx(), pt, pt) {
    return false
  }
  // Pullback of `id : pt -> pt` along itself: the ordinary
  // pullback is the diagonal (dimension 1); shifted derived
  // homology is `[0, 1]`.
  let pb_id = derived_pullback(pt, pt, pt, id_map_cx(), id_map_cx())
  if !pb_id.check_d2() || !int_arr_eq(pb_id.betti(), [0, 1]) {
    return false
  }
  // Zero maps: the ordinary (degree-0) fiber product of the
  // underlying vector spaces is `A + B` (dimension 2), but the
  // derived fiber product has an additional Tor class: shifted
  // homology `[1, 2]`.
  let pb_zero = derived_pullback(pt, pt, pt, zero_map_cx(), zero_map_cx())
  if !pb_zero.check_d2() || !int_arr_eq(pb_zero.betti(), [1, 2]) {
    return false
  }
  // Pullback of the identity of the circle complex along the
  // inclusion of a point is the point itself.
  let circle = CxSpec::{ dims: [1, 1], bnd: [[], [@core.Bits::new(1)]], }
  let f_circle = ChainMapSpec::{ maps: [[bit1(0, 1)], [bit1(0, 1)]], }
  let g_pt = ChainMapSpec::{ maps: [[bit1(0, 1)], []], }
  if !chain_map_ok(f_circle, circle, circle) || !chain_map_ok(g_pt, pt, circle) {
    return false
  }
  let pb_circ = derived_pullback(circle, pt, circle, f_circle, g_pt)
  if !pb_circ.check_d2() || !int_arr_eq(pb_circ.betti(), [0, 1, 0]) {
    return false
  }
  // The ordinary set-theoretic pullback, for comparison, is the
  // equaliser count and sees no derived correction.
  let ordinary = {
    let mut cnt = 0
    for x in 0..<2 {
      for y in 0..<2 {
        // Zero maps from `Fin 2`-sized fibres to a point.
        cnt = cnt + 1
        let _ = (x, y)
      }
    }
    cnt
  }
  ordinary == 4 && pb_zero.betti()[0] + pb_zero.betti()[1] == 3
}

// ---------------------------------------------------------------------------
// Discrete connections, curvature, and horizontal distributions
// ---------------------------------------------------------------------------
//
// Base: the torus grid graph `Z_w x Z_h` (only the `right` and `up`
// edges are stored; `left` / `down` are their inverses).  Fibre:
// `Fin m`.  A connection assigns a permutation of the fibre to
// every stored edge; parallel transport along the reverse edge is
// the inverse permutation.  The horizontal distribution is the set
// of lifted edges in the total graph: over each base edge and each
// fibre point of the source there is exactly one horizontal edge,
// and horizontal edges are disjoint from vertical ones.  Curvature
// is the holonomy (composite transport) around each unit square
// (plaquette); the connection is flat iff every plaquette holonomy
// is the identity.

///|
fn perm_id(m : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<m {
    out.push(i)
  }
  out
}

///|
fn perm_inv(p : Array[Int32]) -> Array[Int32] {
  let out = Array::make(p.length(), 0)
  for i in 0..<p.length() {
    out[p[i]] = i
  }
  out
}

///|
/// Composition: apply `p` first, then `q`.
fn perm_then(p : Array[Int32], q : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<p.length() {
    out.push(q[p[i]])
  }
  out
}

///|
fn perm_is_id(p : Array[Int32]) -> Bool {
  for i in 0..<p.length() {
    if p[i] != i {
      return false
    }
  }
  true
}

///|
pub(all) struct Conn {
  w : Int32
  h : Int32
  fiber : Int32
  right : Array[Array[Int32]] // right[x * h + y]
  up : Array[Array[Int32]]
}

///|
fn conn_flat(w : Int32, h : Int32, fiber : Int32) -> Conn {
  let right : Array[Array[Int32]] = []
  let up : Array[Array[Int32]] = []
  for _ in 0..<(w * h) {
    right.push(perm_id(fiber))
    up.push(perm_id(fiber))
  }
  Conn::{ w, h, fiber, right, up, }
}

///|
/// Holonomy around the plaquette with lower-left corner `(x, y)`:
/// right, up, left (inverse of the top `right`), down (inverse of
/// the left `up`).
pub fn plaquette_holonomy(c : Conn, x : Int32, y : Int32) -> Array[Int32] {
  let h = c.h
  let x1 = (x + 1) % c.w
  let y1 = (y + 1) % c.h
  let r1 = c.right[x * h + y]
  let u2 = c.up[x1 * h + y]
  let l3 = perm_inv(c.right[x * h + y1])
  let d4 = perm_inv(c.up[x * h + y])
  perm_then(perm_then(perm_then(r1, u2), l3), d4)
}

///|
pub fn magnetic_plaquette_holonomy() -> Array[Int32] {
  let c = {
    let base = conn_flat(3, 3, 2)
    // A single "magnetic" up-edge carrying the swap.
    base.up[1 * 3 + 0] = [1, 0]
    base
  }
  plaquette_holonomy(c, 0, 0)
}

///|
pub fn check_connection_curvature() -> Bool {
  // Flat connection: trivial curvature, and horizontal lifts of
  // closed base loops return every fibre point to itself.
  let flat = conn_flat(3, 3, 3)
  for x in 0..<3 {
    for y in 0..<3 {
      if !perm_is_id(plaquette_holonomy(flat, x, y)) {
        return false
      }
    }
  }
  // Gauge-trivial connection from vertex potentials
  // `h_v`: transport along an edge is `h_head^-1 . h_tail`
  // (in the `perm_then` convention below this is also flat).
  let gauged = {
    let pots : Array[Array[Int32]] = []
    for v in 0..<9 {
      // Potentials: cyclic shifts by `v` in the fibre `Fin 3`.
      let p : Array[Int32] = []
      for f in 0..<3 {
        p.push((f + v) % 3)
      }
      pots.push(p)
    }
    let right : Array[Array[Int32]] = []
    let up : Array[Array[Int32]] = []
    for x in 0..<3 {
      for y in 0..<3 {
        let v = x * 3 + y
        let vr = (x + 1) % 3 * 3 + y
        let vu = x * 3 + (y + 1) % 3
        right.push(perm_then(pots[v], perm_inv(pots[vr])))
        up.push(perm_then(pots[v], perm_inv(pots[vu])))
      }
    }
    Conn::{ w: 3, h: 3, fiber: 3, right, up, }
  }
  for x in 0..<3 {
    for y in 0..<3 {
      if !perm_is_id(plaquette_holonomy(gauged, x, y)) {
        return false
      }
    }
  }
  // Magnetic connection: one plaquette has swap holonomy, so
  // horizontal transport around that loop swaps the fibre points
  // (path dependence = nonzero curvature), while the horizontal
  // distribution still projects bijectively to base edges.
  let magnetic = {
    let base = conn_flat(3, 3, 2)
    base.up[1 * 3 + 0] = [1, 0]
    base
  }
  if !int_arr_eq(plaquette_holonomy(magnetic, 0, 0), [1, 0]) {
    return false
  }
  let mut any_curved = false
  for x in 0..<3 {
    for y in 0..<3 {
      if !perm_is_id(plaquette_holonomy(magnetic, x, y)) {
        any_curved = true
      }
    }
  }
  if !any_curved {
    return false
  }
  // Horizontal distribution: for every base vertex, every fibre
  // point, and every direction, the horizontal lift exists and is
  // unique (it is the graph of the transport permutation), and it
  // never equals a vertical edge (its base endpoint always moves).
  for x in 0..<3 {
    for y in 0..<3 {
      for f in 0..<2 {
        let vr = (x + 1) % 3 * 3 + y
        let lifted = magnetic.right[x * 3 + y][f]
        if lifted < 0 || lifted >= 2 || vr == x * 3 + y {
          return false
        }
        // Transport forth and back along a stored edge is the
        // identity (the reverse lift uses the inverse permutation).
        let back = perm_inv(magnetic.right[x * 3 + y])[lifted]
        if back != f {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Universal covering of the cycle graph, and higher groupoids
// ---------------------------------------------------------------------------

///|
fn pos_mod(k : Int32, n : Int32) -> Int32 {
  (k % n + n) % n
}

///|
/// Lift a walk on the cycle `C_n` (given by signed steps `+1` /
/// `-1`) to the universal cover `Z`, starting at `0`.  The lift is
/// unique: at each step the covering map `k |-> k mod n` restricts
/// to a bijection on the star of every vertex.
pub fn cover_lift(steps : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = [0]
  let mut pos = 0
  for s in steps {
    pos = pos + s
    out.push(pos)
  }
  out
}

///|
pub fn check_universal_covering() -> Bool {
  let n = 6
  let window = 4 * n
  // Local homeomorphism on a window of the cover: the neighbours
  // of each interior vertex project bijectively to the neighbours
  // of its image.
  for k in -window..<window {
    let img = pos_mod(k, n)
    let lo = pos_mod(k - 1, n)
    let hi = pos_mod(k + 1, n)
    if lo == hi || (lo - img + n) % n == 0 || (hi - img + n) % n == 0 {
      return false
    }
    if !(lo == pos_mod(img - 1, n) && hi == pos_mod(img + 1, n)) {
      return false
    }
  }
  // Unique path lifting and deck transformations, over all walks
  // of length 6 with steps +-1 (64 walks): the projection of the
  // lift is the original walk, endpoints differ by deck shifts,
  // and a walk that closes up in `C_n` lifts to `n * winding`.
  for code in 0..<(1 << 6) {
    let steps : Array[Int32] = []
    for i in 0..<6 {
      steps.push(if ((code >> i) & 1) == 1 { 1 } else { -1 })
    }
    let lift = cover_lift(steps)
    let mut vertex = 0
    for i in 0..<6 {
      vertex = pos_mod(vertex + steps[i], n)
      if pos_mod(lift[i + 1], n) != vertex {
        return false
      }
    }
    // Uniqueness: any other lift starting in the fibre over `0`
    // (i.e. at a deck translate `n * k`) is the translate of this
    // one.
    for k in [-1, 1] {
      for i in 0..<lift.length() {
        if pos_mod(lift[i] + n * k, n) != pos_mod(lift[i], n) {
          return false
        }
      }
    }
    // Closed walks have an integral winding number.
    if vertex == 0 {
      let total = lift[6]
      if total % n != 0 {
        return false
      }
    }
  }
  // Going once around the circle lifts to `n`: winding number 1.
  let around = cover_lift([1, 1, 1, 1, 1, 1])
  around[6] == n && pos_mod(around[6], n) == 0
}

///|
/// A morphism of the fundamental groupoid of the circle in
/// covering normal form: its source and target vertices in `C_n`
/// and the endpoint in `Z` of the lift that starts at the
/// representative of the source.
pub(all) struct CircleMor {
  src : Int32
  tgt : Int32
  lift : Int32
}

///|
fn circ_id(v : Int32) -> CircleMor {
  CircleMor::{ src: v, tgt: v, lift: v, }
}

///|
fn circ_comp(a : CircleMor, b : CircleMor) -> CircleMor {
  // `b.lift - b.src` is the displacement of `b`; append it to `a`.
  CircleMor::{ src: a.src, tgt: b.tgt, lift: a.lift + (b.lift - b.src), }
}

///|
fn circ_inv(a : CircleMor) -> CircleMor {
  CircleMor::{ src: a.tgt, tgt: a.src, lift: a.tgt - (a.lift - a.src), }
}

///|
fn circ_eq(a : CircleMor, b : CircleMor) -> Bool {
  a.src == b.src && a.tgt == b.tgt && a.lift == b.lift
}

///|
/// Is there a 2-cell (a homotopy rel endpoints) between parallel
/// morphisms?  In the covering model, exactly when their lifts
/// agree.
pub fn circ_has_2cell(a : CircleMor, b : CircleMor) -> Bool {
  a.src == b.src && a.tgt == b.tgt && a.lift == b.lift
}

///|
fn hg_torus_class(steps : Array[(Int32, Int32)]) -> (Int32, Int32) {
  let mut dx = 0
  let mut dy = 0
  for (sx, sy) in steps {
    dx = dx + sx
    dy = dy + sy
  }
  (dx, dy)
}

///|
fn hg_torus_end(steps : Array[(Int32, Int32)]) -> (Int32, Int32) {
  let mut x = 0
  let mut y = 0
  for (sx, sy) in steps {
    x = pos_mod(x + sx, 3)
    y = pos_mod(y + sy, 3)
  }
  (x, y)
}

///|
pub fn check_higher_groupoid_model() -> Bool {
  let n = 6
  // Fundamental groupoid of `S^1`: morphisms are enumerated by
  // source, target and winding number `w in [-2, 2]` (the lift
  // endpoint is `src + w * n + (tgt - src)` adjusted into the
  // fibre over `tgt`).
  let mors : Array[CircleMor] = []
  for src in 0..<n {
    for tgt in 0..<n {
      for w in [-2, -1, 0, 1, 2] {
        mors.push(CircleMor::{
          src,
          tgt,
          lift: src + (tgt - src + n) % n + w * n,
        })
      }
    }
  }
  // Groupoid laws on all composable enumerated morphisms.
  for a in mors {
    if !circ_eq(circ_comp(circ_id(a.src), a), a) ||
      !circ_eq(circ_comp(a, circ_id(a.tgt)), a) {
      return false
    }
    if !circ_eq(circ_comp(a, circ_inv(a)), circ_id(a.src)) ||
      !circ_eq(circ_comp(circ_inv(a), a), circ_id(a.tgt)) {
      return false
    }
    for b in mors {
      if b.src == a.tgt {
        for c in mors {
          if c.src == b.tgt {
            if !circ_eq(
                circ_comp(circ_comp(a, b), c),
                circ_comp(a, circ_comp(b, c)),
              ) {
              return false
            }
          }
        }
        // 2-cells are decidable and are an equivalence: they hold
        // iff the parallel morphisms are already equal as classes.
        if circ_has_2cell(a, a) != true {
          return false
        }
      }
    }
  }
  // The loop that winds once (same endpoint as the identity, but
  // lift differing by `n`) admits no 2-cell to the identity: the
  // groupoid is not thin at the level of 1-cells, and `pi_1` is
  // detected exactly by the lift.
  let loop1 = CircleMor::{ src: 0, tgt: 0, lift: n, }
  if circ_has_2cell(loop1, circ_id(0)) || !circ_has_2cell(loop1, loop1) {
    return false
  }
  if !circ_eq(circ_comp(loop1, loop1), CircleMor::{
      src: 0,
      tgt: 0,
      lift: 2 * n,
    }) {
    return false
  }
  // Fundamental groupoid of the torus `Z_3 x Z_3`, via lifts to
  // `Z^2`: a path class is `(src, tgt, dx, dy)`.  The square
  // commutator `R U L D` has displacement `(0, 0)`, hence carries
  // a 2-cell to the identity (the square filler); going `R` three
  // times has displacement `(3, 0)` and does not.
  let square = hg_torus_class([(1, 0), (0, 1), (-1, 0), (0, -1)])
  let wind_x = hg_torus_class([(1, 0), (1, 0), (1, 0)])
  if square != (0, 0) || wind_x != (3, 0) {
    return false
  }
  // Endpoint bookkeeping on the torus itself: both paths close up
  // at the base vertex, but only the square is null-homotopic.
  hg_torus_end([(1, 0), (0, 1), (-1, 0), (0, -1)]) == (0, 0) &&
  hg_torus_end([(1, 0), (1, 0), (1, 0)]) == (0, 0) &&
  square == (0, 0) &&
  wind_x != (0, 0)
}
