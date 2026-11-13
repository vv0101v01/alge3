///|
// Stable spectra, fast leaf FFT, and the cyclic butterfly FFT.
//
// The transform is the NTT over `F_p` with `p = 998244353`
// (primitive root 3), so every identity below is exact -- this is
// the finite-field sense of "stable spectrum": no rounding, the
// transform is exactly invertible, cyclic shifts act on the
// spectrum by exact twiddle factors (shift theorem), and the
// Parseval identity `sum_k X_k X_{-k} = n * sum_j a_j^2` holds on
// the nose.  Three implementations are verified against each
// other and against the naive DFT matrix:
//   * `ntt_butterfly`: iterative, bit-reversed leaves, in place;
//   * `ntt_recursive`:  leaf recursion -- the spectrum of the
//     whole signal is glued from the spectra of the even and odd
//     leaves by twiddle factors (the spectral-sheaf gluing);
//   * `ntt_naive`:    the DFT matrix itself.
// Linear and cyclic convolutions are computed through the
// butterfly and checked against their naive definitions.

///|
pub fn nx_fft_prime() -> Int32 {
  998244353
}

///|
fn nx_mod(x : Int32) -> Int32 {
  let p = nx_fft_prime()
  let r = x % p
  if r < 0 {
    r + p
  } else {
    r
  }
}

///|
fn nx_mod64(x : Int64) -> Int32 {
  let p = nx_fft_prime().to_int64()
  let r = x % p
  (if r < 0L { r + p } else { r }).to_int()
}

///|
pub fn nx_mod_mul(a : Int32, b : Int32) -> Int32 {
  nx_mod64(a.to_int64() * b.to_int64())
}

///|
pub fn nx_mod_pow(a : Int32, e : Int32) -> Int32 {
  let mut result = 1
  let mut base = nx_mod(a)
  let mut exp = e
  while exp > 0 {
    if exp % 2 == 1 {
      result = nx_mod_mul(result, base)
    }
    base = nx_mod_mul(base, base)
    exp = exp / 2
  }
  result
}

///|
pub fn nx_mod_inv(a : Int32) -> Int32 {
  nx_mod_pow(a, nx_fft_prime() - 2)
}

///|
fn nx_add(a : Int32, b : Int32) -> Int32 {
  nx_mod(a + b)
}

///|
fn nx_sub(a : Int32, b : Int32) -> Int32 {
  nx_mod(a - b)
}

///|
/// The primitive `n`-th root of unity used by all three
/// implementations (`n` a power of two).
pub fn nx_root(n : Int32) -> Int32 {
  nx_mod_pow(3, (nx_fft_prime() - 1) / n)
}

///|
fn nx_signal(n : Int32, seed : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<n {
    out.push((i * i * 7 + i * seed + seed * 3 + 1) % 89)
  }
  out
}

///|
/// The naive DFT: `X_k = sum_j a_j * w^(j k)`.
pub fn ntt_naive(a : Array[Int32]) -> Array[Int32] {
  let n = a.length()
  let w = nx_root(n)
  let out : Array[Int32] = []
  for k in 0..<n {
    let mut acc = 0
    for j in 0..<n {
      acc = nx_add(acc, nx_mod_mul(a[j], nx_mod_pow(w, j * k % n)))
    }
    out.push(acc)
  }
  out
}

///|
fn nx_bit_reverse(x : Int32, bits : Int32) -> Int32 {
  let mut r = 0
  for i in 0..<bits {
    if ((x >> i) & 1) == 1 {
      r = r | (1 << (bits - 1 - i))
    }
  }
  r
}

///|
fn nx_log2(n : Int32) -> Int32 {
  let mut r = 0
  let mut m = n
  while m > 1 {
    m = m / 2
    r = r + 1
  }
  r
}

///|
/// Iterative butterfly NTT (bit-reversed leaves, in place on a
/// copy).  With `invert`, the inverse transform (inverse root,
/// scaled by `1/n`).
pub fn ntt_butterfly(a : Array[Int32], invert : Bool) -> Array[Int32] {
  let n = a.length()
  let bits = nx_log2(n)
  let out : Array[Int32] = []
  for i in 0..<n {
    out.push(a[nx_bit_reverse(i, bits)])
  }
  let mut len = 2
  while len <= n {
    let mut wlen = nx_mod_pow(nx_root(len), 1)
    if invert {
      wlen = nx_mod_inv(wlen)
    }
    let half = len / 2
    let mut block = 0
    while block < n {
      let mut w = 1
      for j in 0..<half {
        let u = out[block + j]
        let v = nx_mod_mul(out[block + j + half], w)
        out[block + j] = nx_add(u, v)
        out[block + j + half] = nx_sub(u, v)
        w = nx_mod_mul(w, wlen)
      }
      block = block + len
    }
    len = len * 2
  }
  if invert {
    let inv_n = nx_mod_inv(n)
    for i in 0..<n {
      out[i] = nx_mod_mul(out[i], inv_n)
    }
  }
  out
}

///|
/// Recursive ("leaf") NTT: split into even/odd leaves, transform
/// the leaves, and glue the two leaf spectra with twiddle
/// factors.  This is the divide-and-conquer recursion of the
/// butterfly, written as a sheaf-style gluing of local spectra.
pub fn ntt_recursive(a : Array[Int32]) -> Array[Int32] {
  let n = a.length()
  if n == 1 {
    return [a[0]]
  }
  let even : Array[Int32] = []
  let odd : Array[Int32] = []
  for i in 0..<n {
    if i % 2 == 0 {
      even.push(a[i])
    } else {
      odd.push(a[i])
    }
  }
  let e = ntt_recursive(even)
  let o = ntt_recursive(odd)
  let w = nx_root(n)
  let out : Array[Int32] = []
  for _ in 0..<n {
    out.push(0)
  }
  let mut wk = 1
  for k in 0..<(n / 2) {
    let t = nx_mod_mul(wk, o[k])
    out[k] = nx_add(e[k], t)
    out[k + n / 2] = nx_sub(e[k], t)
    wk = nx_mod_mul(wk, w)
  }
  out
}

///|
/// The number of butterfly operations: `(n/2) log2 n`.
pub fn nx_butterfly_op_count(n : Int32) -> Int32 {
  n / 2 * nx_log2(n)
}

///|
fn nx_arr_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    if a[i] != b[i] {
      return false
    }
  }
  true
}

///|
/// Linear convolution by NTT (zero-padded to a power of two).
pub fn nx_convolve(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let need = a.length() + b.length() - 1
  let mut n = 1
  while n < need {
    n = n * 2
  }
  let fa : Array[Int32] = []
  let fb : Array[Int32] = []
  for i in 0..<n {
    fa.push(if i < a.length() { a[i] } else { 0 })
    fb.push(if i < b.length() { b[i] } else { 0 })
  }
  let xa = ntt_butterfly(fa, false)
  let xb = ntt_butterfly(fb, false)
  let prod : Array[Int32] = []
  for i in 0..<n {
    prod.push(nx_mod_mul(xa[i], xb[i]))
  }
  let all = ntt_butterfly(prod, true)
  let out : Array[Int32] = []
  for i in 0..<need {
    out.push(all[i])
  }
  out
}

///|
fn nx_convolve_naive(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<(a.length() + b.length() - 1) {
    out.push(0)
  }
  for i in 0..<a.length() {
    for j in 0..<b.length() {
      out[i + j] = nx_add(out[i + j], nx_mod_mul(a[i], b[j]))
    }
  }
  out
}

///|
/// Cyclic convolution of length `n` (wrap-around), by NTT.
pub fn nx_cyclic_convolve(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let xa = ntt_butterfly(a, false)
  let xb = ntt_butterfly(b, false)
  let prod : Array[Int32] = []
  for i in 0..<a.length() {
    prod.push(nx_mod_mul(xa[i], xb[i]))
  }
  ntt_butterfly(prod, true)
}

///|
fn nx_cyclic_convolve_naive(a : Array[Int32], b : Array[Int32]) -> Array[Int32] {
  let n = a.length()
  let out : Array[Int32] = []
  for _ in 0..<n {
    out.push(0)
  }
  for i in 0..<n {
    for j in 0..<n {
      out[(i + j) % n] = nx_add(out[(i + j) % n], nx_mod_mul(a[i], b[j]))
    }
  }
  out
}

///|
pub fn check_stable_spectral_fft() -> Bool {
  // Butterfly = recursive = naive, exactly, and the transform is
  // exactly invertible (round trip is the identity): stability.
  for n in [4, 8, 16] {
    let a = nx_signal(n, 5)
    let naive = ntt_naive(a)
    if !nx_arr_eq(ntt_butterfly(a, false), naive) {
      return false
    }
    if !nx_arr_eq(ntt_recursive(a), naive) {
      return false
    }
    if !nx_arr_eq(ntt_butterfly(naive, true), a) {
      return false
    }
  }
  // Butterfly operation count.
  if nx_butterfly_op_count(16) != 32 || nx_butterfly_op_count(8) != 12 {
    return false
  }
  // Shift theorem: a cyclic shift of the signal multiplies the
  // spectrum by exact twiddle factors.
  let n = 8
  let s = 3
  let a = nx_signal(n, 2)
  let shifted : Array[Int32] = []
  for j in 0..<n {
    shifted.push(a[(j - s + n * 2) % n])
  }
  let xa = ntt_naive(a)
  let xb = ntt_naive(shifted)
  let w = nx_root(n)
  for k in 0..<n {
    if xb[k] != nx_mod_mul(nx_mod_pow(w, s * k % n), xa[k]) {
      return false
    }
  }
  // Parseval identity over F_p: sum_k X_k X_{-k} = n sum_j a_j^2.
  let mut lhs = 0
  for k in 0..<n {
    lhs = nx_add(lhs, nx_mod_mul(xa[k], xa[(n - k) % n]))
  }
  let mut rhs = 0
  for j in 0..<n {
    rhs = nx_add(rhs, nx_mod_mul(a[j], a[j]))
  }
  rhs = nx_mod_mul(n, rhs)
  if lhs != rhs {
    return false
  }
  // Spectral-sheaf gluing: the length-8 spectrum is glued from
  // the even/odd leaf spectra of length 4 by twiddles (checked
  // directly, not only through the recursive implementation).
  let even : Array[Int32] = []
  let odd : Array[Int32] = []
  for i in 0..<n {
    if i % 2 == 0 {
      even.push(a[i])
    } else {
      odd.push(a[i])
    }
  }
  let e = ntt_naive(even)
  let o = ntt_naive(odd)
  for k in 0..<4 {
    let t = nx_mod_mul(nx_mod_pow(w, k), o[k])
    if xa[k] != nx_add(e[k], t) || xa[k + 4] != nx_sub(e[k], t) {
      return false
    }
  }
  // Linear convolution through the butterfly.
  let ca = [3, 1, 4, 1, 5]
  let cb = [9, 2, 6, 5]
  nx_arr_eq(nx_convolve(ca, cb), nx_convolve_naive(ca, cb))
}

///|
pub fn check_cyclic_butterfly_fft() -> Bool {
  let a = nx_signal(8, 3)
  let b = nx_signal(8, 7)
  if !nx_arr_eq(nx_cyclic_convolve(a, b), nx_cyclic_convolve_naive(a, b)) {
    return false
  }
  // Wrap-around sanity: cyclic convolution with a unit impulse at
  // position 1 is the cyclic shift by 1.
  let impulse : Array[Int32] = []
  for i in 0..<8 {
    impulse.push(if i == 1 { 1 } else { 0 })
  }
  let shifted = nx_cyclic_convolve(a, impulse)
  for j in 0..<8 {
    if shifted[j] != a[(j - 1 + 8) % 8] {
      return false
    }
  }
  true
}
