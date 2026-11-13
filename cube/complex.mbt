///|
// Complex scalars, vectors and matrices backing numeric Kan cubes (`cube.mbt`).

///|
pub(all) struct Complex {
  re : Double
  im : Double
}

///|
pub type CVec = Array[Complex]

///|
pub type CMat = Array[Array[Complex]]

///|
pub fn c_make(re : Double, im : Double) -> Complex {
  Complex::{ re, im, }
}

///|
pub fn c_zero() -> Complex {
  Complex::{ re: 0.0, im: 0.0, }
}

///|
pub fn c_one() -> Complex {
  Complex::{ re: 1.0, im: 0.0, }
}

///|
pub fn c_real(x : Double) -> Complex {
  Complex::{ re: x, im: 0.0, }
}

///|
pub fn c_add(a : Complex, b : Complex) -> Complex {
  Complex::{ re: a.re + b.re, im: a.im + b.im, }
}

///|
pub fn c_sub(a : Complex, b : Complex) -> Complex {
  Complex::{ re: a.re - b.re, im: a.im - b.im, }
}

///|
pub fn c_mul(a : Complex, b : Complex) -> Complex {
  Complex::{ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re, }
}

///|
pub fn c_scale(s : Double, a : Complex) -> Complex {
  Complex::{ re: s * a.re, im: s * a.im, }
}

///|
pub fn c_conj(a : Complex) -> Complex {
  Complex::{ re: a.re, im: -a.im, }
}

///|
pub fn c_abs2(a : Complex) -> Double {
  a.re * a.re + a.im * a.im
}

///|
pub fn vec_add(a : CVec, b : CVec) -> CVec {
  let n = a.length()
  let out : CVec = []
  for i in 0..<n {
    out.push(c_add(a[i], b[i]))
  }
  out
}

///|
pub fn vec_sub(a : CVec, b : CVec) -> CVec {
  let n = a.length()
  let out : CVec = []
  for i in 0..<n {
    out.push(c_sub(a[i], b[i]))
  }
  out
}

///|
pub fn vec_scale(s : Double, a : CVec) -> CVec {
  let n = a.length()
  let out : CVec = []
  for i in 0..<n {
    out.push(c_scale(s, a[i]))
  }
  out
}

///|
pub fn vec_approx_eq(a : CVec, b : CVec) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let tol = 1.0e-9
  for i in 0..<a.length() {
    let diff = c_sub(a[i], b[i])
    if diff.re * diff.re + diff.im * diff.im > tol * tol {
      return false
    }
  }
  true
}

///|
/// Apply the eigenspace projection matrix `p` (`P² = P`) to `v`.
pub fn prune_to_eigenspace(p : CMat, v : CVec) -> CVec {
  let out : CVec = []
  for i in 0..<p.length() {
    let row = p[i]
    let mut acc = c_zero()
    for j in 0..<row.length() {
      if j < v.length() {
        acc = c_add(acc, c_mul(row[j], v[j]))
      }
    }
    out.push(acc)
  }
  out
}

///|
/// Membership in `im(P)` checked via the retraction condition `P v ≈ v`.
pub fn in_image(p : CMat, v : CVec) -> Bool {
  vec_approx_eq(prune_to_eigenspace(p, v), v)
}
