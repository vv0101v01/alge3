///|
/// A finite monoid: a one-object category.  `mul[i][j]` is `i * j`, and `e`
/// is the identity.  The nerve `N(M)` is the bar construction: its `k`-cells
/// are `k`-tuples `(a_1, ..., a_k)` of elements, with face maps given by
/// dropping an entry or multiplying two adjacent entries.
pub struct Monoid {
  n : Int32
  e : Int32
  mul : Array[Array[Int32]]
}

///|
pub fn Monoid::new(mul : Array[Array[Int32]], e : Int32) -> Monoid {
  Monoid::{ n: mul.length(), e, mul, }
}

///|
pub fn Monoid::is_associative(self : Monoid) -> Bool {
  let mut ok = true
  for a in 0..<self.n {
    for b in 0..<self.n {
      for c in 0..<self.n {
        if self.mul[self.mul[a][b]][c] != self.mul[a][self.mul[b][c]] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
pub fn Monoid::is_unital(self : Monoid) -> Bool {
  let mut ok = true
  for a in 0..<self.n {
    if self.mul[self.e][a] != a || self.mul[a][self.e] != a {
      ok = false
    }
  }
  ok
}

///|
fn pow_int(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<exp {
    r = r * base
  }
  r
}

///|
/// Decode a `0..n^k` index into its `k` base-`n` digits (least significant
/// digit first).
fn digits_of(idx : Int32, k : Int32, n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut x = idx
  for _ in 0..<k {
    out.push(x % n)
    x = x / n
  }
  out
}

///|
fn encode_digits(ds : Array[Int32], n : Int32) -> Int32 {
  let mut idx = 0
  let mut p = 1
  for d in ds {
    idx = idx + d * p
    p = p * n
  }
  idx
}

///|
/// The `i`-th face of a `k`-tuple, encoded in `C_{k-1}`.
fn bar_face(m : Monoid, idx : Int32, k : Int32, i : Int32) -> Int32 {
  let ds = digits_of(idx, k, m.n)
  if i == 0 {
    // drop the first entry
    let tail : Array[Int32] = []
    for t in 1..<k {
      tail.push(ds[t])
    }
    encode_digits(tail, m.n)
  } else if i == k {
    // drop the last entry
    let init : Array[Int32] = []
    for t in 0..<(k - 1) {
      init.push(ds[t])
    }
    encode_digits(init, m.n)
  } else {
    // multiply entries i-1 and i (0-based), then drop position i
    let out : Array[Int32] = []
    for t in 0..<k {
      if t == i - 1 {
        out.push(m.mul[ds[i - 1]][ds[i]])
      } else if t != i {
        out.push(ds[t])
      }
    }
    encode_digits(out, m.n)
  }
}

///|
/// Bar complex `C_k = F_2[M^k]`, `k = 0..maxdeg`, with the alternating sum of
/// face maps.  Over `F_2` the signs disappear and the differential is the XOR
/// of all `k+1` faces.
pub fn bar_complex(m : Monoid, maxdeg : Int32) -> ChainComplex {
  let dims : Array[Int32] = []
  for k in 0..<=maxdeg {
    dims.push(pow_int(m.n, k))
  }
  let boundaries : Array[Array[Bits]] = []
  boundaries.push([])
  for k in 1..<=maxdeg {
    let cols : Array[Bits] = []
    let count = pow_int(m.n, k)
    for idx in 0..<count {
      let b = Bits::new(pow_int(m.n, k - 1))
      for i in 0..<=k {
        b.flip(bar_face(m, idx, k, i))
      }
      cols.push(b)
    }
    boundaries.push(cols)
  }
  ChainComplex::new(dims, boundaries)
}

///|
/// Homology of the classifying space `B M` in degrees `0..maxdeg`.
pub fn bar_betti(m : Monoid, maxdeg : Int32) -> Array[Int32] {
  // Build one degree higher so that the top Betti number is honest
  // (otherwise `H_maxdeg` would be computed with `d_{maxdeg+1}` missing).
  let full = bar_complex(m, maxdeg + 1).betti()
  let out : Array[Int32] = []
  for k in 0..<=maxdeg {
    out.push(full[k])
  }
  out
}

///|
/// The cyclic group `Z/n`, written multiplicatively as `{0, ..., n-1}`.
pub fn cyclic_group(n : Int32) -> Monoid {
  let mul : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push((i + j) % n)
    }
    mul.push(row)
  }
  Monoid::new(mul, 0)
}

///|
/// The trivial monoid `{e}`; `B{1}` is contractible.
pub fn trivial_monoid() -> Monoid {
  Monoid::new([[0]], 0)
}
