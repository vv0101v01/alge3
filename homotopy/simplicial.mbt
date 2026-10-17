///|
/// A finite simplicial complex, stored dimension by dimension.
/// A simplex on vertices `< 64` is encoded as a `UInt64` bitmask; the mask's
/// popcount minus one is its dimension.
pub struct SimplicialComplex {
  simplices : Array[Array[UInt64]]
}

///|
using @core {type Bits, type BoolMat, type ChainComplex}

///|
pub fn mask_of(verts : Array[Int32]) -> UInt64 {
  let mut m = 0UL
  for v in verts {
    m = m | (1UL << v)
  }
  m
}

///|
pub fn mask_popcount(x : UInt64) -> Int32 {
  @core.popcount64(x)
}

///|
fn sort_u64(a : Array[UInt64]) -> Unit {
  // insertion sort; simplex counts in the examples are small
  for i in 1..<a.length() {
    let x = a[i]
    let mut j = i - 1
    let mut done = false
    while j >= 0 && !done {
      if a[j] > x {
        a[j + 1] = a[j]
        j = j - 1
      } else {
        done = true
      }
    }
    a[j + 1] = x
  }
}

///|
fn dedup_sorted(a : Array[UInt64]) -> Array[UInt64] {
  let out : Array[UInt64] = []
  let mut last = 0UL
  let mut first = true
  for x in a {
    if first || x != last {
      out.push(x)
      last = x
      first = false
    }
  }
  out
}

///|
pub fn SimplicialComplex::from_maximal(
  maximal : Array[UInt64],
) -> SimplicialComplex {
  let buckets : Array[Array[UInt64]] = []
  for _ in 0..<12 {
    buckets.push([])
  }
  for m in maximal {
    let d = mask_popcount(m)
    if d > 0 && d <= 11 {
      let mut sub = m
      while true {
        if sub != 0UL {
          let dd = mask_popcount(sub) - 1
          buckets[dd].push(sub)
        }
        if sub == 0UL {
          break
        }
        sub = (sub - 1UL) & m
      }
    }
  }
  let out : Array[Array[UInt64]] = []
  for d in 0..<12 {
    sort_u64(buckets[d])
    out.push(dedup_sorted(buckets[d]))
  }
  SimplicialComplex::{ simplices: out, }
}

///|
pub fn SimplicialComplex::dim(self : SimplicialComplex) -> Int32 {
  let mut d = 0
  for k in 0..<self.simplices.length() {
    if self.simplices[k].length() > 0 {
      d = k
    }
  }
  d
}

///|
pub fn SimplicialComplex::count(self : SimplicialComplex, k : Int32) -> Int32 {
  if k < 0 || k >= self.simplices.length() {
    0
  } else {
    self.simplices[k].length()
  }
}

///|
pub fn SimplicialComplex::has(self : SimplicialComplex, m : UInt64) -> Bool {
  let d = mask_popcount(m) - 1
  if d < 0 || d >= self.simplices.length() {
    false
  } else {
    let arr = self.simplices[d]
    let mut lo = 0
    let mut hi = arr.length() - 1
    let mut found = false
    while lo <= hi {
      let mid = (lo + hi) / 2
      if arr[mid] == m {
        found = true
        lo = hi + 1
      } else if arr[mid] < m {
        lo = mid + 1
      } else {
        hi = mid - 1
      }
    }
    found
  }
}

///|
fn index_of(arr : Array[UInt64], m : UInt64) -> Int32 {
  let mut lo = 0
  let mut hi = arr.length() - 1
  let mut ans = -1
  while lo <= hi {
    let mid = (lo + hi) / 2
    if arr[mid] == m {
      ans = mid
      lo = hi + 1
    } else if arr[mid] < m {
      lo = mid + 1
    } else {
      hi = mid - 1
    }
  }
  ans
}

///|
/// Boundary columns of the simplicial chain complex.  Over `F_2` the signs in
/// `d[v_0...v_k] = sum_i (-1)^i [v_0...v_i^...v_k]` all disappear, so the
/// boundary of a simplex is simply the XOR of its codimension-one faces.
pub fn SimplicialComplex::boundary_columns(
  self : SimplicialComplex,
  k : Int32,
) -> Array[Bits] {
  let cols : Array[Bits] = []
  if k <= 0 || k >= self.simplices.length() {
    return cols
  }
  let prev = self.simplices[k - 1]
  for m in self.simplices[k] {
    let b = Bits::new(prev.length())
    let mut x = m
    while x != 0UL {
      let v = @core.trailing_zeros64(x)
      let face = m ^ (1UL << v)
      let idx = index_of(prev, face)
      if idx >= 0 {
        b.set(idx)
      }
      x = x & (x - 1UL)
    }
    cols.push(b)
  }
  cols
}

///|
pub fn SimplicialComplex::to_chain(self : SimplicialComplex) -> ChainComplex {
  let top = self.dim()
  let dims : Array[Int32] = []
  for k in 0..<=top {
    dims.push(self.simplices[k].length())
  }
  let boundaries : Array[Array[Bits]] = []
  boundaries.push([])
  for k in 1..<=top {
    boundaries.push(self.boundary_columns(k))
  }
  ChainComplex::new(dims, boundaries)
}

///|
pub fn SimplicialComplex::betti(self : SimplicialComplex) -> Array[Int32] {
  self.to_chain().betti()
}

///|
pub fn SimplicialComplex::euler(self : SimplicialComplex) -> Int32 {
  self.to_chain().euler()
}

///|
/// The standard 3-vertex triangulation of `S^1`.
pub fn circle() -> SimplicialComplex {
  SimplicialComplex::from_maximal([
    mask_of([0, 1]),
    mask_of([1, 2]),
    mask_of([2, 0]),
  ])
}

///|
/// Boundary of the 3-simplex: a triangulation of `S^2` with 4 vertices.
pub fn sphere() -> SimplicialComplex {
  SimplicialComplex::from_maximal([
    mask_of([0, 1, 2]),
    mask_of([0, 1, 3]),
    mask_of([0, 2, 3]),
    mask_of([1, 2, 3]),
  ])
}

///|
/// The 4-vertex boundary of the 3-simplex, as a full 3-dimensional complex
/// (used to test inner-horn filling).
pub fn simplex3() -> SimplicialComplex {
  SimplicialComplex::from_maximal([mask_of([0, 1, 2, 3])])
}

///|
/// 3 x 3 grid on the torus: 9 vertices, 18 triangles, `chi = 0`.
pub fn torus() -> SimplicialComplex {
  let tris : Array[UInt64] = []
  for i in 0..<3 {
    for j in 0..<3 {
      let a = i * 3 + j
      let b = (i + 1) % 3 * 3 + j
      let c = (i + 1) % 3 * 3 + (j + 1) % 3
      let d = i * 3 + (j + 1) % 3
      tris.push(mask_of([a, b, c]))
      tris.push(mask_of([a, c, d]))
    }
  }
  SimplicialComplex::from_maximal(tris)
}

///|
/// The 12 vertices and 20 faces of the icosahedron (standard coordinates,
/// generated combinatorially by the 5-triangle fans around two poles).
fn icosahedron_faces() -> Array[UInt64] {
  let faces : Array[Array[Int32]] = [
    [0, 1, 8],
    [0, 8, 4],
    [0, 4, 5],
    [0, 5, 9],
    [0, 9, 1],
    [1, 6, 8],
    [8, 6, 10],
    [8, 10, 4],
    [4, 10, 2],
    [4, 2, 5],
    [5, 2, 11],
    [5, 11, 9],
    [9, 11, 7],
    [9, 7, 1],
    [1, 7, 6],
    [6, 7, 3],
    [6, 3, 10],
    [10, 3, 2],
    [2, 3, 11],
    [11, 3, 7],
  ]
  let out : Array[UInt64] = []
  for f in faces {
    out.push(mask_of(f))
  }
  out
}

///|
/// `RP^2` as the antipodal quotient of the icosahedron: 6 vertices, 15 edges,
/// 10 triangles.  This is the unique vertex-minimal triangulation.
pub fn projective_plane() -> SimplicialComplex {
  let q : Array[Int32] = [0, 1, 1, 0, 2, 3, 3, 2, 4, 5, 5, 4]
  let faces = icosahedron_faces()
  let tris : Array[UInt64] = []
  for f in faces {
    let vs : Array[Int32] = []
    let mut x = f
    while x != 0UL {
      let v = @core.trailing_zeros64(x)
      vs.push(q[v])
      x = x & (x - 1UL)
    }
    tris.push(mask_of(vs))
  }
  SimplicialComplex::from_maximal(tris)
}

///|
/// `RP^2` minus one open triangle is a Möbius band (`chi = 0`,
/// `H_* = (1,1,0)` over `F_2`).
pub fn mobius_band() -> SimplicialComplex {
  let rp = projective_plane()
  let faces = rp.simplices[2]
  let maximal : Array[UInt64] = []
  for i in 1..<faces.length() {
    maximal.push(faces[i])
  }
  SimplicialComplex::from_maximal(maximal)
}

///|
/// Check inner-horn filling in dimension 2: every composable pair of edges
/// `(i,j), (j,k)` must be filled by a triangle `(i,j,k)`.
pub fn fills_inner_horns_2(cx : SimplicialComplex) -> Bool {
  let edges = cx.simplices[1]
  let mut ok = true
  for e1 in edges {
    let vs1 : Array[Int32] = []
    let mut x = e1
    while x != 0UL {
      vs1.push(@core.trailing_zeros64(x))
      x = x & (x - 1UL)
    }
    for e2 in edges {
      // share exactly one vertex j, and e1 != e2
      if e1 != e2 {
        let shared = e1 & e2
        if shared != 0UL && mask_popcount(shared) == 1 {
          let j = @core.trailing_zeros64(shared)
          let i = if vs1[0] == j { vs1[1] } else { vs1[0] }
          let other = e2 ^ shared
          let k = @core.trailing_zeros64(other)
          if i != k && !cx.has(mask_of([i, j, k])) {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// Check inner-horn filling in dimension 3.  For each 4-set of vertices, the
/// inner horns `Lambda^3_1` and `Lambda^3_2` (three of the four faces present)
/// must be filled by a 3-simplex.
pub fn fills_inner_horns_3(cx : SimplicialComplex) -> Bool {
  if cx.simplices.length() < 4 {
    return false
  }
  let n = cx.simplices[0].length()
  let mut ok = true
  for a in 0..<n {
    for b in (a + 1)..<n {
      for c in (b + 1)..<n {
        for d in (c + 1)..<n {
          let vs = [a, b, c, d]
          let full = mask_of(vs)
          let faces : Array[UInt64] = [
            mask_of([b, c, d]),
            mask_of([a, c, d]),
            mask_of([a, b, d]),
            mask_of([a, b, c]),
          ]
          // inner horn k=1 omits face d1; k=2 omits d2
          for missing in [1, 2] {
            let mut count = 0
            for i in 0..<4 {
              if i != missing && cx.has(faces[i]) {
                count = count + 1
              }
            }
            if count == 3 && !cx.has(full) {
              ok = false
            }
          }
        }
      }
    }
  }
  ok
}

///|
pub fn complex_summary(name : String, cx : SimplicialComplex) -> String {
  let sb = StringBuilder()
  sb.write_string(name)
  sb.write_string(": ")
  sb.write_string("V=")
  sb.write_string(cx.count(0).to_string())
  sb.write_string(" E=")
  sb.write_string(cx.count(1).to_string())
  sb.write_string(" F=")
  sb.write_string(cx.count(2).to_string())
  sb.write_string(" chi=")
  sb.write_string(cx.euler().to_string())
  sb.write_string(" beta=")
  sb.write_string(@core.ints_to_s(cx.betti()))
  sb.to_string()
}
