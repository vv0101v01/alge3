///|
/// Arithmetic in the prime field `F_p` for a small prime `p`.  All elements
/// are represented by `Int` in `[0, p)`.
pub fn fp_norm(x : Int32, p : Int32) -> Int32 {
  let mut y = x % p
  if y < 0 {
    y = y + p
  }
  y
}

///|
pub fn fp_add(x : Int32, y : Int32, p : Int32) -> Int32 {
  fp_norm(x + y, p)
}

///|
pub fn fp_sub(x : Int32, y : Int32, p : Int32) -> Int32 {
  fp_norm(x - y, p)
}

///|
pub fn fp_mul(x : Int32, y : Int32, p : Int32) -> Int32 {
  fp_norm(x * y, p)
}

///|
/// Extended Euclidean inverse in `F_p` (works for any prime `p`).
pub fn fp_inv(a : Int32, p : Int32) -> Int32 {
  let mut old_r = fp_norm(a, p)
  let mut r = p
  let mut old_s = 1
  let mut s = 0
  while r != 0 {
    let q = old_r / r
    let nr = old_r - q * r
    old_r = r
    r = nr
    let ns = old_s - q * s
    old_s = s
    s = ns
  }
  fp_norm(old_s, p)
}

///|
/// Rank of a dense matrix over `F_p` by Gauss-Jordan elimination.
/// `rows[i][j]`, `0 <= i < m`, `0 <= j < n`.
pub fn fp_rank(rows : Array[Array[Int32]], p : Int32) -> Int32 {
  let m = rows.length()
  let n = if m == 0 { 0 } else { rows[0].length() }
  let a : Array[Array[Int32]] = []
  for i in 0..<m {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(fp_norm(rows[i][j], p))
    }
    a.push(row)
  }
  let mut r = 0
  for c in 0..<n {
    let mut piv = -1
    let mut i = r
    while i < m {
      if a[i][c] != 0 {
        piv = i
      }
      if piv >= 0 {
        i = m
      } else {
        i = i + 1
      }
    }
    if piv >= 0 {
      if piv != r {
        let tmp = a[r]
        a[r] = a[piv]
        a[piv] = tmp
      }
      let inv = fp_inv(a[r][c], p)
      for j in c..<n {
        a[r][j] = fp_mul(a[r][j], inv, p)
      }
      for i2 in 0..<m {
        if i2 != r && a[i2][c] != 0 {
          let f = a[i2][c]
          for j in c..<n {
            a[i2][j] = fp_sub(a[i2][j], fp_mul(f, a[r][j], p), p)
          }
        }
      }
      r = r + 1
    }
  }
  r
}

///|
/// Determinant over `F_p` (Gaussian elimination without normalising rows).
pub fn fp_det(rows : Array[Array[Int32]], p : Int32) -> Int32 {
  let n = rows.length()
  let a : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(fp_norm(rows[i][j], p))
    }
    a.push(row)
  }
  let mut det = 1
  for c in 0..<n {
    let mut piv = -1
    for i in c..<n {
      if a[i][c] != 0 && piv < 0 {
        piv = i
      }
    }
    if piv < 0 {
      det = 0
    } else {
      if piv != c {
        let tmp = a[c]
        a[c] = a[piv]
        a[piv] = tmp
        det = fp_sub(0, det, p)
      }
      let pivot = a[c][c]
      det = fp_mul(det, pivot, p)
      let inv = fp_inv(pivot, p)
      for i in (c + 1)..<n {
        if a[i][c] != 0 {
          let f = fp_mul(a[i][c], inv, p)
          for j in c..<n {
            a[i][j] = fp_sub(a[i][j], fp_mul(f, a[c][j], p), p)
          }
        }
      }
    }
  }
  det
}
