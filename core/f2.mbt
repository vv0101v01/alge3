///|
/// Row-major Boolean matrix: `rows[i]` is a bit vector of length `ncols`.
/// Matrices over GF(2) are stored row-wise so that multiplication is
/// "for each set bit j of row i, XOR row j of B with the accumulator".
pub struct BoolMat {
  rows : Array[Bits]
  ncols : Int32
}

///|
pub fn BoolMat::new(rows : Array[Bits], ncols : Int32) -> BoolMat {
  BoolMat::{ rows, ncols, }
}

///|
pub fn BoolMat::nrows(self : BoolMat) -> Int32 {
  self.rows.length()
}

///|
pub fn BoolMat::get(self : BoolMat, i : Int32, j : Int32) -> Bool {
  self.rows[i].get(j)
}

///|
pub fn BoolMat::zero(m : Int32, n : Int32) -> BoolMat {
  let rows : Array[Bits] = []
  for _ in 0..<m {
    rows.push(Bits::new(n))
  }
  BoolMat::{ rows, ncols: n, }
}

///|
pub fn BoolMat::identity(n : Int32) -> BoolMat {
  let rows : Array[Bits] = []
  for i in 0..<n {
    let r = Bits::new(n)
    r.set(i)
    rows.push(r)
  }
  BoolMat::{ rows, ncols: n, }
}

///|
/// Boolean (GF(2)) matrix product.  Cost: `O(m * k * w)` word operations,
/// where `w = ncols / 64`; this is the bit-parallel speedup of the naive
/// `O(m * k * n)` scalar algorithm.
pub fn BoolMat::mul(self : BoolMat, other : BoolMat) -> BoolMat {
  let rows : Array[Bits] = []
  for i in 0..<self.rows.length() {
    let acc = Bits::new(other.ncols)
    let x = self.rows[i].copy()
    while true {
      match x.first_set() {
        None => break
        Some(j) => {
          acc.xor_inplace(other.rows[j])
          x.clear_bit(j)
        }
      }
    }
    rows.push(acc)
  }
  BoolMat::{ rows, ncols: other.ncols, }
}

///|
/// Boolean-semiring (OR, AND) product, used for spans, relations and
/// profunctors.  Same bit-parallel cost as `mul`.
pub fn BoolMat::mul_or(self : BoolMat, other : BoolMat) -> BoolMat {
  let rows : Array[Bits] = []
  for i in 0..<self.rows.length() {
    let acc = Bits::new(other.ncols)
    let x = self.rows[i].copy()
    for j in 0..<self.ncols {
      if x.get(j) {
        acc.or_inplace(other.rows[j])
      }
    }
    rows.push(acc)
  }
  BoolMat::{ rows, ncols: other.ncols, }
}

///|
pub fn BoolMat::transpose(self : BoolMat) -> BoolMat {
  let rows : Array[Bits] = []
  for _ in 0..<self.ncols {
    rows.push(Bits::new(self.rows.length()))
  }
  for i in 0..<self.rows.length() {
    for j in 0..<self.ncols {
      if self.rows[i].get(j) {
        rows[j].set(i)
      }
    }
  }
  BoolMat::{ rows, ncols: self.rows.length(), }
}

///|
/// Rank over GF(2) of a list of column vectors in `F_2^nrows`.
/// Online elimination with lowest-bit pivots; each column is reduced at most
/// `nrows` times, each reduction costs `nrows/64` word XORs.
pub fn rank(cols : Array[Bits], nrows : Int32) -> Int32 {
  let basis : Array[Bits] = []
  for _ in 0..<nrows {
    basis.push(Bits::new(nrows))
  }
  let mut r = 0
  for c in cols {
    let mut v = c.copy()
    while true {
      match v.first_set() {
        None => break
        Some(p) =>
          if basis[p].is_zero() {
            basis[p] = v
            r = r + 1
            break
          } else {
            v = v.xor(basis[p])
          }
      }
    }
  }
  r
}

///|
/// Rank of a matrix, computed as the rank of its row space.
pub fn rank_mat(m : BoolMat) -> Int32 {
  rank(m.rows, m.ncols)
}

///|
pub fn nullity(ncols : Int32, r : Int32) -> Int32 {
  ncols - r
}

///|
/// Column `j` of a row-major matrix, as a vector over the row index.
pub fn BoolMat::column(self : BoolMat, j : Int32) -> Bits {
  let c = Bits::new(self.rows.length())
  for i in 0..<self.rows.length() {
    if self.rows[i].get(j) {
      c.set(i)
    }
  }
  c
}

///|
/// Verify the Boolean-matrix multiplication against the scalar definition
/// on a small deterministic example (used in tests).
pub fn mul_scalar_reference(a : BoolMat, b : BoolMat) -> BoolMat {
  let m = a.rows.length()
  let n = b.ncols
  let k = b.rows.length()
  let out = BoolMat::zero(m, n)
  for i in 0..<m {
    for j in 0..<n {
      let mut s = false
      for t in 0..<k {
        if a.rows[i].get(t) && b.rows[t].get(j) {
          s = !s
        }
      }
      if s {
        out.rows[i].set(j)
      }
    }
  }
  out
}
