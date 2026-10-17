///|
/// A finite chain complex of `F_2`-vector spaces
/// `... -> C_{k+1} --d_{k+1}--> C_k --d_k--> C_{k-1} -> ...`
/// with `d_k d_{k+1} = 0`.
///
/// `dims[k]` is the dimension of `C_k`; `boundaries[k]` lists the columns of
/// `d_k` as bit vectors over the basis of `C_{k-1}`.  `boundaries[0]` is empty.
pub struct ChainComplex {
  dims : Array[Int32]
  boundaries : Array[Array[Bits]]
}

///|
pub fn ChainComplex::new(
  dims : Array[Int32],
  boundaries : Array[Array[Bits]],
) -> ChainComplex {
  ChainComplex::{ dims, boundaries, }
}

///|
pub fn ChainComplex::top(self : ChainComplex) -> Int32 {
  self.dims.length() - 1
}

///|
pub fn ChainComplex::rank_at(self : ChainComplex, k : Int32) -> Int32 {
  if k <= 0 || k >= self.boundaries.length() {
    0
  } else {
    rank(self.boundaries[k], self.dims[k - 1])
  }
}

///|
/// Betti numbers `b_k = dim C_k - rank d_k - rank d_{k+1}`.
pub fn ChainComplex::betti(self : ChainComplex) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<self.dims.length() {
    let rk = self.rank_at(k)
    let rk1 = self.rank_at(k + 1)
    out.push(self.dims[k] - rk - rk1)
  }
  out
}

///|
pub fn ChainComplex::euler(self : ChainComplex) -> Int32 {
  let mut s = 0
  for k in 0..<self.dims.length() {
    if k % 2 == 0 {
      s = s + self.dims[k]
    } else {
      s = s - self.dims[k]
    }
  }
  s
}

///|
/// Check `d_{k-1} d_k = 0` for every composable pair.  Because the matrices
/// are Boolean, this is exactly: for every column of `d_k`, the XOR of the
/// columns of `d_{k-1}` indexed by its set bits is zero.
pub fn ChainComplex::check_d2(self : ChainComplex) -> Bool {
  let mut ok = true
  for k in 1..<self.boundaries.length() {
    if k >= 1 && self.boundaries[k].length() > 0 {
      for col in self.boundaries[k] {
        let acc = Bits::new(self.dims[k - 1])
        let x = col.copy()
        while true {
          match x.first_set() {
            None => break
            Some(i) => {
              if k - 1 >= 1 && i < self.boundaries[k - 1].length() {
                acc.xor_inplace(self.boundaries[k - 1][i])
              }
              x.clear_bit(i)
            }
          }
        }
        if !acc.is_zero() {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// Total dimension of the complex (sum of all `C_k`), used for cost estimates.
pub fn ChainComplex::total_dim(self : ChainComplex) -> Int32 {
  let mut s = 0
  for d in self.dims {
    s = s + d
  }
  s
}

///|
pub fn ints_to_s(xs : Array[Int32]) -> String {
  let sb = StringBuilder()
  sb.write_string("[")
  for i in 0..<xs.length() {
    if i > 0 {
      sb.write_string(", ")
    }
    sb.write_string(xs[i].to_string())
  }
  sb.write_string("]")
  sb.to_string()
}

///|
/// Homology dimensions as a record with all intermediate ranks, useful for
/// the benchmark report.
pub fn ChainComplex::profile(self : ChainComplex) -> String {
  let sb = StringBuilder()
  sb.write_string("dims=")
  sb.write_string(ints_to_s(self.dims))
  sb.write_string(" ranks=")
  let rs : Array[Int32] = []
  for k in 0..<self.dims.length() {
    rs.push(self.rank_at(k))
  }
  sb.write_string(ints_to_s(rs))
  sb.write_string(" betti=")
  sb.write_string(ints_to_s(self.betti()))
  sb.to_string()
}
