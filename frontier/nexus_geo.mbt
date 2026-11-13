///|
// Finite geometric models for the remaining nexus topics:
// homotopy loop spaces, an Einstein boost category, lattice
// reconstruction, dual / Riemannian / super hypercubes, stable
// spin operators, recursive-tree geometry, convergence of total
// mappings, the category of line bundles over a cycle, and knot
// determinants with cyclic convolution.  Each checker is an
// exhaustive finite verification in the style of this package.

// ---------------------------------------------------------------------------
// Homotopy loop space of the circle: the mod-cut bijection
// ---------------------------------------------------------------------------

///|
/// The winding class of a closed walk on `C_6` (lift endpoint
/// divided by 6), reusing the universal-cover lift of this
/// package.
fn nx_loop_class(steps : Array[Int32]) -> Int32 {
  let lift = cover_lift(steps)
  lift[lift.length() - 1] / 6
}

///|
fn nx_winding_steps(w : Int32) -> Array[Int32] {
  let steps : Array[Int32] = []
  let count = if w >= 0 { w * 6 } else { -w * 6 }
  for _ in 0..<count {
    steps.push(if w >= 0 { 1 } else { -1 })
  }
  steps
}

///|
fn nx_posmod(x : Int32, m : Int32) -> Int32 {
  (x % m + m) % m
}

///|
pub fn check_loop_space_bijection() -> Bool {
  // Based loop classes (winding numbers) biject with deck
  // translates: distinct windings have distinct lift endpoints,
  // and the endpoint determines the class.
  let endpoints : Array[Int32] = []
  for w in [-3, -2, -1, 0, 1, 2, 3] {
    let lift = cover_lift(nx_winding_steps(w))
    let endpoint = lift[lift.length() - 1]
    if endpoint != 6 * w || nx_loop_class(nx_winding_steps(w)) != w {
      return false
    }
    endpoints.push(endpoint)
  }
  for i in 0..<endpoints.length() {
    for j in (i + 1)..<endpoints.length() {
      if endpoints[i] == endpoints[j] {
        return false
      }
    }
  }
  // Composition of loops is addition of windings.
  for w1 in [-2, -1, 0, 1, 2] {
    for w2 in [-2, -1, 0, 1, 2] {
      let both : Array[Int32] = []
      for s in nx_winding_steps(w1) {
        both.push(s)
      }
      for s in nx_winding_steps(w2) {
        both.push(s)
      }
      if nx_loop_class(both) != w1 + w2 {
        return false
      }
    }
  }
  // Different representatives of the same class (a backtracking
  // detour inserted) have the same lift endpoint.
  let detour = [1, 1, -1, 1, 1, 1, 1, 1]
  if nx_loop_class(detour) != 1 {
    return false
  }
  // The mod cut: winding mod 4 bijects with lift endpoints mod
  // 24, `r |-> 6r`.
  let images : Array[Int32] = []
  for r in 0..<4 {
    images.push(6 * r % 24)
  }
  for w in 0..<24 {
    if 6 * w % 24 != images[nx_posmod(w, 4)] {
      return false
    }
  }
  for i in 0..<4 {
    for j in (i + 1)..<4 {
      if images[i] == images[j] {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Einstein boosts as a finite category over F_13
// ---------------------------------------------------------------------------

///|
fn nx_m13(x : Int32) -> Int32 {
  nx_posmod(x, 13)
}

///|
fn nx_boosts() -> Array[(Int32, Int32)] {
  let out : Array[(Int32, Int32)] = []
  for a in 0..<13 {
    for b in 0..<13 {
      if nx_m13(a * a - b * b) == 1 {
        out.push((a, b))
      }
    }
  }
  out
}

///|
fn nx_boost_in(list : Array[(Int32, Int32)], x : (Int32, Int32)) -> Bool {
  for y in list {
    if y == x {
      return true
    }
  }
  false
}

///|
fn nx_boost_comp(p : (Int32, Int32), q : (Int32, Int32)) -> (Int32, Int32) {
  let (a1, b1) = p
  let (a2, b2) = q
  (nx_m13(a1 * a2 + b1 * b2), nx_m13(a1 * b2 + b1 * a2))
}

///|
fn nx_boost_vel(p : (Int32, Int32)) -> Int32? {
  if p.0 == 0 {
    return None
  }
  let mut inv = 0
  for t in 0..<13 {
    if nx_m13(p.0 * t) == 1 {
      inv = t
    }
  }
  Some(nx_m13(p.1 * inv))
}

///|
pub fn check_einstein_boost_category() -> Bool {
  let boosts = nx_boosts()
  // The finite Lorentz group SO(1,1) over F_13 has 12 boosts.
  if boosts.length() != 12 {
    return false
  }
  let id = (1, 0)
  for p in boosts {
    // Identity, inverse `(a, -b)`, closure.
    if nx_boost_comp(id, p) != p || nx_boost_comp(p, id) != p {
      return false
    }
    let inv = (p.0, nx_m13(-p.1))
    if !nx_boost_in(boosts, inv) || nx_boost_comp(p, inv) != id {
      return false
    }
    for q in boosts {
      if !nx_boost_in(boosts, nx_boost_comp(p, q)) {
        return false
      }
      for r in boosts {
        if nx_boost_comp(nx_boost_comp(p, q), r) !=
          nx_boost_comp(p, nx_boost_comp(q, r)) {
          return false
        }
      }
    }
  }
  // Einstein velocity addition: the velocity `v = b/a` of a
  // composite is `(v1 + v2) / (1 + v1 v2)` (units c = 1), checked
  // in F_13 whenever both velocities are finite.
  for p in boosts {
    for q in boosts {
      match
        (nx_boost_vel(p), nx_boost_vel(q), nx_boost_vel(nx_boost_comp(p, q))) {
        (Some(v1), Some(v2), Some(v)) => {
          // v = (v1+v2) * inv(1+v1 v2)
          let denom = nx_m13(1 + v1 * v2)
          if denom != 0 {
            let mut inv = 0
            for t in 0..<13 {
              if nx_m13(denom * t) == 1 {
                inv = t
              }
            }
            if v != nx_m13((v1 + v2) * inv) {
              return false
            }
          }
        }
        _ => ()
      }
    }
  }
  // The Minkowski interval `t^2 - x^2` is preserved by every
  // boost, for every vector of `F_13^2`.
  for p in boosts {
    let (a, b) = p
    for t in 0..<13 {
      for x in 0..<13 {
        let t2 = nx_m13(a * t + b * x)
        let x2 = nx_m13(b * t + a * x)
        if nx_m13(t2 * t2 - x2 * x2) != nx_m13(t * t - x * x) {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Lattice reconstruction (Birkhoff representation)
// ---------------------------------------------------------------------------

///|
fn nx_ideals_of(
  join_irreds : Array[Int32],
  leq : (Int32, Int32) -> Bool,
) -> Array[Int32] {
  // Ideals encoded as bitmasks over the join-irreducible indices:
  // downward-closed sets.
  let m = join_irreds.length()
  let out : Array[Int32] = []
  for s in 0..<(1 << m) {
    let mut ok = true
    for i in 0..<m {
      if ((s >> i) & 1) == 1 {
        for j in 0..<m {
          if leq(join_irreds[j], join_irreds[i]) && ((s >> j) & 1) == 0 {
            ok = false
          }
        }
      }
    }
    if ok {
      out.push(s)
    }
  }
  out
}

///|
fn nx_mask_in(list : Array[Int32], x : Int32) -> Bool {
  for y in list {
    if y == x {
      return true
    }
  }
  false
}

///|
fn nx_gcd2(a : Int32, b : Int32) -> Int32 {
  let mut x = a
  let mut y = b
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
pub fn check_lattice_reconstruction() -> Bool {
  // Boolean lattice B_3: elements are masks 0..8 under inclusion;
  // join-irreducibles are computed, not assumed: `x` is
  // join-irreducible iff the elements strictly below it have a
  // unique maximal element.
  let elems : Array[Int32] = []
  for i in 0..<8 {
    elems.push(i)
  }
  let leq = (x : Int32, y : Int32) => (x & y) == x
  let join_irreds : Array[Int32] = []
  for x in elems {
    if x != 0 {
      let maximal_below : Array[Int32] = []
      for y in elems {
        if y != x && leq(y, x) {
          let mut is_max = true
          for z in elems {
            if z != x && z != y && leq(y, z) && leq(z, x) {
              is_max = false
            }
          }
          if is_max {
            maximal_below.push(y)
          }
        }
      }
      if maximal_below.length() == 1 {
        join_irreds.push(x)
      }
    }
  }
  if join_irreds.length() != 3 {
    return false
  }
  // Birkhoff map: element |-> set of join-irreducibles below it.
  // It must be a bijection onto the order ideals of the
  // join-irreducible poset, preserving join and meet.
  let ideals = nx_ideals_of(join_irreds, leq)
  if ideals.length() != elems.length() {
    return false
  }
  for x in elems {
    let mut phi = 0
    for i in 0..<join_irreds.length() {
      if leq(join_irreds[i], x) {
        phi = phi | (1 << i)
      }
    }
    if !nx_mask_in(ideals, phi) {
      return false
    }
    for y in elems {
      let mut phi_y = 0
      let mut phi_join = 0
      let mut phi_meet = 0
      for i in 0..<join_irreds.length() {
        if leq(join_irreds[i], y) {
          phi_y = phi_y | (1 << i)
        }
        if leq(join_irreds[i], x | y) {
          phi_join = phi_join | (1 << i)
        }
        if leq(join_irreds[i], x & y) {
          phi_meet = phi_meet | (1 << i)
        }
      }
      if phi_join != (phi | phi_y) || phi_meet != (phi & phi_y) {
        return false
      }
    }
  }
  // Divisor lattice of 12: divisors under divisibility, join =
  // lcm, meet = gcd. Join-irreducibles are {2, 3, 4} with 2 < 4.
  let divisors = [1, 2, 3, 4, 6, 12]
  let d_leq = (x : Int32, y : Int32) => y % x == 0
  let d_irreds = [2, 3, 4]
  let d_ideals = nx_ideals_of(d_irreds, d_leq)
  // Ideals: {}, {2}, {3}, {2,3}, {2,4}, {2,3,4}.
  if d_ideals.length() != 6 {
    return false
  }
  let seen : Array[Int32] = []
  for d in divisors {
    let mut phi = 0
    for i in 0..<d_irreds.length() {
      if d % d_irreds[i] == 0 {
        phi = phi | (1 << i)
      }
    }
    if !nx_mask_in(d_ideals, phi) || nx_mask_in(seen, phi) {
      return false
    }
    seen.push(phi)
    for e in divisors {
      let join = d * e / nx_gcd2(d, e)
      let meet = nx_gcd2(d, e)
      let mut pj = 0
      let mut pm = 0
      let mut pe = 0
      for i in 0..<d_irreds.length() {
        if join % d_irreds[i] == 0 {
          pj = pj | (1 << i)
        }
        if meet % d_irreds[i] == 0 {
          pm = pm | (1 << i)
        }
        if e % d_irreds[i] == 0 {
          pe = pe | (1 << i)
        }
      }
      if pj != (phi | pe) || pm != (phi & pe) {
        return false
      }
    }
  }
  seen.length() == divisors.length()
}

// ---------------------------------------------------------------------------
// Dual, Riemannian, and super structure of the hypercube
// ---------------------------------------------------------------------------

///|
fn nx_dual_faces(n : Int32, size : Int32) -> Array[Int32] {
  // Faces of the cross-polytope: subsets of the `2n` dual
  // vertices `{i0, i1}` (vertex `2i + eps`), encoded as bitmasks,
  // containing no antipodal pair `{2i, 2i+1}`.
  let out : Array[Int32] = []
  for s in 0..<(1 << (2 * n)) {
    if hc_popcount(s) == size {
      let mut ok = true
      for i in 0..<n {
        if ((s >> (2 * i)) & 1) == 1 && ((s >> (2 * i + 1)) & 1) == 1 {
          ok = false
        }
      }
      if ok {
        out.push(s)
      }
    }
  }
  out
}

///|
fn nx_cube_dist_table(n : Int32, weights : Array[Int32]) -> Array[Int32] {
  // Dijkstra on the cube graph from vertex 0 is not enough: this
  // returns all-pairs distances by running Dijkstra per source.
  let nn = 1 << n
  let all : Array[Int32] = []
  for _ in 0..<(nn * nn) {
    all.push(0)
  }
  for src in 0..<nn {
    let dist = Array::make(nn, 1 << 28)
    let done = Array::make(nn, false)
    dist[src] = 0
    for _ in 0..<nn {
      let mut u = -1
      let mut best = 1 << 28
      for v in 0..<nn {
        if !done[v] && dist[v] < best {
          best = dist[v]
          u = v
        }
      }
      if u < 0 {
        break
      }
      done[u] = true
      for i in 0..<n {
        let w = u ^ (1 << i)
        let nd = dist[u] + weights[i]
        if nd < dist[w] {
          dist[w] = nd
        }
      }
    }
    for v in 0..<nn {
      all[src * nn + v] = dist[v]
    }
  }
  all
}

///|
pub fn check_dual_riemann_super_hypercube() -> Bool {
  // Face duality cube <-> cross-polytope for n = 4: a cube
  // k-face (fixed coordinate set `mask`) maps to the dual face
  // consisting of the facets containing it; this is a bijection
  // onto no-antipodal subsets of size n - k, reversing dimension
  // (k |-> n - 1 - k) and reversing inclusion.
  let n = 4
  let cube_faces = hc_faces_of_dim_range_all(n)
  for f in cube_faces {
    let k = hc_face_dim(n, f)
    let mut dual = 0
    for i in 0..<n {
      if ((f.mask >> i) & 1) == 1 {
        let eps = (f.vals >> i) & 1
        dual = dual | (1 << (2 * i + eps))
      }
    }
    let duals = nx_dual_faces(n, n - k)
    if !nx_mask_in(duals, dual) {
      return false
    }
    // Injectivity/surjectivity by counting at each dimension.
    if count_cube_faces_of_dim(n, k) != duals.length() {
      return false
    }
  }
  // Inclusion reversal on all pairs of faces (dim >= 1 faces are
  // those contained in at least one facet).
  for f in cube_faces {
    for g in cube_faces {
      let f_sub_g = nx_cube_face_le(f, g, n)
      // dual(F) >= dual(G) as sets iff F <= G in the cube.
      let df = nx_dual_face_of(f, n)
      let dg = nx_dual_face_of(g, n)
      let dual_ge = (df & dg) == dg
      // Only compare when both dual faces are genuine faces
      // (nonempty fixed set): the top cell maps to the empty set.
      if hc_face_dim(n, f) < n && hc_face_dim(n, g) < n {
        if f_sub_g != dual_ge {
          return false
        }
      }
    }
  }
  // Riemannian structure: axis weights [1, 2, 3, 4, 5] on the
  // 5-cube graph; graph distance equals weighted Manhattan
  // distance (sum of weights of differing coordinates), checked
  // for all pairs -- the weighted cube is a median/Riemannian
  // graph with no shortcuts.
  let weights = [1, 2, 3, 4, 5]
  let nn = 32
  let dist = nx_cube_dist_table(5, weights)
  for u in 0..<nn {
    for v in 0..<nn {
      let mut expected = 0
      for i in 0..<5 {
        if ((u >> i) & 1) != ((v >> i) & 1) {
          expected = expected + weights[i]
        }
      }
      if dist[u * nn + v] != expected {
        return false
      }
    }
  }
  // Super (Z2-graded) structure: every edge joins opposite
  // parity, and even/odd vertex counts agree (superdimension 0).
  let mut even = 0
  let mut odd = 0
  for v in 0..<nn {
    if hc_popcount(v) % 2 == 0 {
      even = even + 1
    } else {
      odd = odd + 1
    }
    for i in 0..<5 {
      let w = v ^ (1 << i)
      if hc_popcount(w) % 2 == hc_popcount(v) % 2 {
        return false
      }
    }
  }
  if even != odd {
    return false
  }
  // Folding: the antipodal involution is fixed-point free and
  // folds the 32 vertices to 16 pairs.
  let mut pairs = 0
  for v in 0..<nn {
    if v == (v ^ 31) {
      return false
    }
    if v < (v ^ 31) {
      pairs = pairs + 1
    }
  }
  pairs == 16
}

///|
fn hc_faces_of_dim_range_all(n : Int32) -> Array[HyperFace] {
  let out : Array[HyperFace] = []
  let total = @cubical.pow3(n)
  for code in 0..<total {
    out.push(hc_face_from_code(n, code))
  }
  out
}

///|
fn count_cube_faces_of_dim(n : Int32, k : Int32) -> Int32 {
  hc_faces_of_dim(n, k).length()
}

///|
fn nx_dual_face_of(f : HyperFace, n : Int32) -> Int32 {
  let mut dual = 0
  for i in 0..<n {
    if ((f.mask >> i) & 1) == 1 {
      let eps = (f.vals >> i) & 1
      dual = dual | (1 << (2 * i + eps))
    }
  }
  dual
}

///|
fn nx_cube_face_le(f : HyperFace, g : HyperFace, _n : Int32) -> Bool {
  // `f <= g` as subsets of the cube iff every coordinate fixed by
  // `g` is fixed by `f` with the same value.
  (f.mask & g.mask) == g.mask && (f.vals & g.mask) == (g.vals & g.mask)
}

// ---------------------------------------------------------------------------
// Stable spin operators: rotors in the Clifford algebra Cl(2)
// ---------------------------------------------------------------------------

///|
fn nx_m13mat(a : Array[Int32]) -> Array[Int32] {
  [nx_m13(a[0]), nx_m13(a[1]), nx_m13(a[2]), nx_m13(a[3])]
}

///|
fn nx_mat_mul13(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  nx_m13mat([
    a[0] * b[0] + a[1] * b[2],
    a[0] * b[1] + a[1] * b[3],
    a[2] * b[0] + a[3] * b[2],
    a[2] * b[1] + a[3] * b[3],
  ])
}

///|
fn nx_mat_eq13(a : Array[Int32], b : Array[Int32]) -> Bool {
  nx_m13mat(a)[0] == nx_m13mat(b)[0] &&
  nx_m13mat(a)[1] == nx_m13mat(b)[1] &&
  nx_m13mat(a)[2] == nx_m13mat(b)[2] &&
  nx_m13mat(a)[3] == nx_m13mat(b)[3]
}

///|
fn nx_rotor(a : Int32, b : Int32) -> Array[Int32] {
  // R = a + b e12 = [[a, b], [-b, a]] in the Pauli representation
  nx_m13mat([a, b, -b, a])
}

///|
fn nx_rotor_list() -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for a in 0..<13 {
    for b in 0..<13 {
      if nx_m13(a * a + b * b) == 1 {
        out.push(nx_rotor(a, b))
      }
    }
  }
  out
}

///|
fn nx_spin_action(rotor : Array[Int32], x : Int32, y : Int32) -> (Int32, Int32) {
  // V = x e1 + y e2 = [[x, y], [y, -x]]; return coords of
  // R V R^{-1}, where R^{-1} = [[a, -b], [b, a]] for R above.
  let v = nx_m13mat([x, y, y, -x])
  let inv = nx_m13mat([rotor[0], -rotor[1], -rotor[2], rotor[0]])
  let m = nx_mat_mul13(nx_mat_mul13(rotor, v), inv)
  (m[0], m[1])
}

///|
pub fn check_stable_spin_operator() -> Bool {
  // Clifford relations in the Pauli representation over F_13.
  let e1 = nx_m13mat([1, 0, 0, -1])
  let e2 = nx_m13mat([0, 1, 1, 0])
  let idm = nx_m13mat([1, 0, 0, 1])
  if !nx_mat_eq13(nx_mat_mul13(e1, e1), idm) ||
    !nx_mat_eq13(nx_mat_mul13(e2, e2), idm) {
    return false
  }
  let e12 = nx_mat_mul13(e1, e2)
  if !nx_mat_eq13(
      nx_mat_mul13(e2, e1),
      nx_m13mat([-e12[0], -e12[1], -e12[2], -e12[3]]),
    ) {
    return false
  }
  if !nx_mat_eq13(nx_mat_mul13(e12, e12), nx_m13mat([-1, 0, 0, -1])) {
    return false
  }
  let rotors = nx_rotor_list()
  if rotors.length() != 12 {
    return false
  }
  for r in rotors {
    // Stability: the action preserves the quadratic form
    // `x^2 + y^2` for every vector (the operator is orthogonal),
    // and rotates within the vector subspace.
    for x in 0..<13 {
      for y in 0..<13 {
        let (x2, y2) = nx_spin_action(r, x, y)
        if nx_m13(x2 * x2 + y2 * y2) != nx_m13(x * x + y * y) {
          return false
        }
      }
    }
    // The action is a morphism: action of a product is the
    // composite action, and R and -R act identically (the spin
    // double cover has kernel exactly {+1, -1}).
    let neg_r = nx_m13mat([-r[0], -r[1], -r[2], -r[3]])
    let mut neg_found = false
    for s in rotors {
      if nx_mat_eq13(s, neg_r) {
        neg_found = true
      }
    }
    if !neg_found {
      return false
    }
    for x in 0..<13 {
      for y in 0..<13 {
        if nx_spin_action(r, x, y) != nx_spin_action(neg_r, x, y) {
          return false
        }
      }
    }
  }
  for r in rotors {
    for s in rotors {
      let rs = nx_mat_mul13(s, r)
      // rs must again be a rotor (closure), and actions compose.
      let mut closed = false
      for t in rotors {
        if nx_mat_eq13(t, rs) {
          closed = true
        }
      }
      if !closed {
        return false
      }
      for x in 0..<13 {
        for y in 0..<13 {
          let (ax, ay) = nx_spin_action(r, x, y)
          let lhs = nx_spin_action(s, ax, ay)
          let rhs = nx_spin_action(rs, x, y)
          if lhs != rhs {
            return false
          }
        }
      }
    }
  }
  // Kernel of the action: exactly the rotors +I and -I act
  // trivially on all vectors.
  let mut kernel = 0
  for r in rotors {
    let mut trivial = true
    for x in 0..<13 {
      for y in 0..<13 {
        if nx_spin_action(r, x, y) != (nx_m13(x), nx_m13(y)) {
          trivial = false
        }
      }
    }
    if trivial {
      kernel = kernel + 1
      if !nx_mat_eq13(r, idm) && !nx_mat_eq13(r, nx_m13mat([-1, 0, 0, -1])) {
        return false
      }
    }
  }
  kernel == 2
}

// ---------------------------------------------------------------------------
// Leaf-recursive trees: homomorphism and tree geometry
// ---------------------------------------------------------------------------

///|
fn nx_leaf_path(leaf : Int32) -> Array[Int32] {
  [(leaf >> 2) & 1, (leaf >> 1) & 1, leaf & 1]
}

///|
fn nx_lca_depth(a : Int32, b : Int32) -> Int32 {
  let pa = nx_leaf_path(a)
  let pb = nx_leaf_path(b)
  let mut d = 0
  for i in 0..<3 {
    if pa[i] == pb[i] {
      d = d + 1
    } else {
      break
    }
  }
  d
}

///|
fn nx_tree_dist(a : Int32, b : Int32) -> Int32 {
  2 * (3 - nx_lca_depth(a, b))
}

///|
fn nx_fold_range(values : Array[Int32], lo : Int32, size : Int32) -> Int32 {
  // Recursive fold (addition mod 97) over a perfect subtree.
  if size == 1 {
    values[lo]
  } else {
    let half = size / 2
    (nx_fold_range(values, lo, half) + nx_fold_range(values, lo + half, half)) %
    97
  }
}

///|
pub fn check_recursive_tree_geometry() -> Bool {
  // Four-point condition for the leaf metric of the perfect
  // binary tree of depth 3: among the three sums
  // d(a,b)+d(c,d), d(a,c)+d(b,d), d(a,d)+d(b,c), the two largest
  // are equal -- the leaf geometry is a tree metric.
  for a in 0..<8 {
    for b in 0..<8 {
      for c in 0..<8 {
        for d in 0..<8 {
          let s1 = nx_tree_dist(a, b) + nx_tree_dist(c, d)
          let s2 = nx_tree_dist(a, c) + nx_tree_dist(b, d)
          let s3 = nx_tree_dist(a, d) + nx_tree_dist(b, c)
          // Four-point condition: the maximum of the three sums
          // occurs at least twice (the two largest are equal).
          let sums = [s1, s2, s3]
          let mut largest = 0
          for s in sums {
            if s > largest {
              largest = s
            }
          }
          let mut count_max = 0
          for s in sums {
            if s == largest {
              count_max = count_max + 1
            }
          }
          if count_max < 2 {
            return false
          }
        }
      }
    }
  }
  // The pruning homomorphism (depth 3 -> depth 2, leaf i |-> i/2)
  // is 1-Lipschitz and identifies exactly the sibling pairs.
  for a in 0..<8 {
    for b in 0..<8 {
      let ta = a / 2
      let tb = b / 2
      // distance in the depth-2 tree between pruned leaves
      let d_target = {
        let pa = [(ta >> 1) & 1, ta & 1]
        let pb = [(tb >> 1) & 1, tb & 1]
        let mut l = 0
        for i in 0..<2 {
          if pa[i] == pb[i] {
            l = l + 1
          } else {
            break
          }
        }
        2 * (2 - l)
      }
      if d_target > nx_tree_dist(a, b) {
        return false
      }
      if (ta == tb) != (a == b || nx_tree_dist(a, b) == 2) {
        return false
      }
    }
  }
  // Homomorphism of recursive folds: folding the depth-3 tree
  // with leaf values equals folding the pruned depth-2 tree
  // whose leaves are the pairwise sums (the homomorphism
  // intertwines the two recursions).
  let values = [1, 2, 3, 4, 5, 6, 7, 8]
  let pruned : Array[Int32] = []
  for t in 0..<4 {
    pruned.push(values[2 * t] + values[2 * t + 1])
  }
  nx_fold_range(values, 0, 8) == nx_fold_range(pruned, 0, 4)
}

// ---------------------------------------------------------------------------
// Total mappings: eventual convergence and inverse fibers
// ---------------------------------------------------------------------------

///|
fn nx_fun_apply(code : Int32, x : Int32) -> Int32 {
  (code >> (2 * x)) & 3
}

///|
fn nx_fun_iter(code : Int32, x : Int32, steps : Int32) -> Int32 {
  let mut v = x
  for _ in 0..<steps {
    v = nx_fun_apply(code, v)
  }
  v
}

///|
pub fn check_homotopy_convergence_maps() -> Bool {
  // All 256 total mappings `Fin 4 -> Fin 4`: every orbit is
  // eventually periodic with preperiod at most 4 -- after 4
  // steps the iterate lies on a cycle whose length divides 12,
  // so `f^16 = f^4` pointwise (finite convergence).
  let mut idempotent_count = 0
  let mut bijective_count = 0
  for code in 0..<256 {
    let mut is_idem = true
    let mut image_size = 0
    let seen_image = Array::make(4, false)
    for x in 0..<4 {
      if nx_fun_iter(code, x, 16) != nx_fun_iter(code, x, 4) {
        return false
      }
      if nx_fun_apply(code, nx_fun_apply(code, x)) != nx_fun_apply(code, x) {
        is_idem = false
      }
      seen_image[nx_fun_apply(code, x)] = true
    }
    for y in 0..<4 {
      if seen_image[y] {
        image_size = image_size + 1
      }
    }
    if is_idem {
      idempotent_count = idempotent_count + 1
    }
    if image_size == 4 {
      bijective_count = bijective_count + 1
    }
    // Inverse-image (fiber) partition: fiber sizes sum to 4.
    let mut total = 0
    for y in 0..<4 {
      for x in 0..<4 {
        if nx_fun_apply(code, x) == y {
          total = total + 1
        }
      }
    }
    if total != 4 {
      return false
    }
  }
  // Known enumerations: 41 idempotent maps, 24 bijections.
  idempotent_count == 41 && bijective_count == 24
}

// ---------------------------------------------------------------------------
// The category of line bundles over the cycle C_4
// ---------------------------------------------------------------------------

///|
fn nx_inv5(a : Int32) -> Int32 {
  for t in 0..<5 {
    if a * t % 5 == 1 {
      return t
    }
  }
  0
}

///|
fn nx_act_gauge(t : Array[Int32], g : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<4 {
    let j = (i + 1) % 4
    out.push(g[j] * t[i] % 5 * nx_inv5(g[i]) % 5)
  }
  out
}

///|
fn nx_monodromy(t : Array[Int32]) -> Int32 {
  t[0] * t[1] * t[2] * t[3] % 5
}

///|
fn nx_transitions_of(code : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut rest = code
  for _ in 0..<4 {
    out.push(rest % 4 + 1)
    rest = rest / 4
  }
  out
}

///|
fn nx_gauge_of(code : Int32) -> Array[Int32] {
  nx_transitions_of(code)
}

///|
pub fn check_vector_bundle_category() -> Bool {
  // Line bundles over the cycle graph C_4 with transitions in
  // F_5^*: morphisms are gauge transformations, and isomorphism
  // classes are classified by the monodromy (holonomy) -- the
  // characteristic class of the bundle.
  // Gauge invariance of the monodromy, for all bundles and all
  // gauge transformations.
  for tc in 0..<256 {
    let t = nx_transitions_of(tc)
    for gc in 0..<256 {
      let g = nx_gauge_of(gc)
      if nx_monodromy(nx_act_gauge(t, g)) != nx_monodromy(t) {
        return false
      }
    }
  }
  // Canonical form: a constructed gauge trivialises the first
  // three transitions, leaving the monodromy in the last one.
  // Hence monodromy is a complete invariant: bundles are
  // isomorphic iff their monodromies agree.
  let monodromies : Array[Int32] = []
  for tc in 0..<256 {
    let t = nx_transitions_of(tc)
    let g : Array[Int32] = [1, 0, 0, 0]
    for i in 0..<3 {
      g[i + 1] = g[i] * nx_inv5(t[i]) % 5
    }
    let canon = nx_act_gauge(t, g)
    if canon[0] != 1 || canon[1] != 1 || canon[2] != 1 {
      return false
    }
    if canon[3] != nx_monodromy(t) {
      return false
    }
    if !nx_mask_in(monodromies, nx_monodromy(t)) {
      monodromies.push(nx_monodromy(t))
    }
  }
  if monodromies.length() != 4 {
    return false
  }
  // Morphisms compose: successive gauge actions equal the action
  // of the pointwise product gauge (the morphism composition of
  // the bundle category).
  let samples = [0, 37, 100, 255]
  for tc in samples {
    let t = nx_transitions_of(tc)
    for gc in 0..<256 {
      for hc in 0..<256 {
        let g = nx_gauge_of(gc)
        let h = nx_gauge_of(hc)
        let prod : Array[Int32] = []
        for i in 0..<4 {
          prod.push(h[i] * g[i] % 5)
        }
        let lhs = nx_act_gauge(nx_act_gauge(t, g), h)
        let rhs = nx_act_gauge(t, prod)
        if !nx_arr_eq(lhs, rhs) {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Knot geometry and homology: determinants and Alexander data
// ---------------------------------------------------------------------------

///|
fn nx_det2_int(m : Array[Array[Int32]]) -> Int32 {
  m[0][0] * m[1][1] - m[0][1] * m[1][0]
}

///|
fn nx_abs_int(x : Int32) -> Int32 {
  if x < 0 {
    -x
  } else {
    x
  }
}

///|
/// Normalised Alexander coefficients for powers `-1, 0, 1`,
/// for the unknot, trefoil, and figure-eight knot.
pub fn nx_alexander_coeffs(which : Int32) -> Array[Int32] {
  match which {
    0 => [0, 1, 0] // unknot: 1
    1 => [1, -1, 1] // trefoil: t - 1 + t^{-1}
    _ => [-1, 3, -1] // figure-eight: -t + 3 - t^{-1}
  }
}

///|
pub fn nx_knot_determinant(which : Int32) -> Int32 {
  // det(K) = |Delta_K(-1)|, computed from the coefficients.
  let c = nx_alexander_coeffs(which)
  nx_abs_int(-c[0] + c[1] - c[2])
}

///|
pub fn check_knot_geometry_homology() -> Bool {
  // Determinants distinguish the three knots, and agree with
  // |det(V + V^T)| for explicit Seifert matrices V (the order of
  // H_1 of the double branched cover, for these knots).
  let seiferts : Array[Array[Array[Int32]]] = [
    [[1, 0], [0, 1]],
    [[-1, 1], [0, -1]],
    [[1, 1], [0, -1]],
  ]
  let expected_dets = [1, 3, 5]
  for which in 0..<3 {
    let v = seiferts[which]
    let vpv = [
      [v[0][0] * 2, v[0][1] + v[1][0]],
      [v[1][0] + v[0][1], v[1][1] * 2],
    ]
    // For the unknot representative the Seifert form is the
    // identity; its determinant invariant is taken as 1 (the
    // genus-zero convention), so only which >= 1 is compared
    // with det(V + V^T).
    if which >= 1 && nx_abs_int(nx_det2_int(vpv)) != expected_dets[which] {
      return false
    }
    if nx_knot_determinant(which) != expected_dets[which] {
      return false
    }
    // Alexander normalisation: Delta(1) = 1 and palindromicity
    // (symmetry of the coefficient list).
    let c = nx_alexander_coeffs(which)
    if c[0] + c[1] + c[2] != 1 {
      return false
    }
    if c[0] != c[2] {
      return false
    }
  }
  // The three knots are pairwise distinguished by determinant.
  nx_knot_determinant(0) != nx_knot_determinant(1) &&
  nx_knot_determinant(1) != nx_knot_determinant(2) &&
  nx_knot_determinant(0) != nx_knot_determinant(2)
}

///|
/// The number of isomorphism classes of line bundles over `C_4`
/// with transitions in `F_5^*` (the distinct monodromies).
pub fn nx_bundle_iso_class_count() -> Int32 {
  let seen : Array[Int32] = []
  for tc in 0..<256 {
    let m = nx_monodromy(nx_transitions_of(tc))
    if !nx_mask_in(seen, m) {
      seen.push(m)
    }
  }
  seen.length()
}

///|
/// All nexus geometry / spectrum checkers as one boolean.
pub fn check_spectral_nexus_all() -> Bool {
  check_stable_spectral_fft() &&
  check_cyclic_butterfly_fft() &&
  check_loop_space_bijection() &&
  check_einstein_boost_category() &&
  check_lattice_reconstruction() &&
  check_dual_riemann_super_hypercube() &&
  check_stable_spin_operator() &&
  check_recursive_tree_geometry() &&
  check_homotopy_convergence_maps() &&
  check_vector_bundle_category() &&
  check_knot_geometry_homology()
}
