///|
/// Non-degenerate surjections `[r+d] -> [r]` generate the arity-`r` component
/// of the McClure–Smith surjection operad in degree `d`.  This is an `E_∞`
/// operad: every component is contractible (checked below) and the operad is
/// `Σ`-free.
pub fn e_word_count(r : Int32, d : Int32) -> Int32 {
  let len = r + d
  let total = pow_int(r, len)
  let mut count = 0
  for code in 0..<total {
    let w = decode_word(code, len, r)
    if word_surjective(w, r) && word_nondegenerate(w) {
      count = count + 1
    }
  }
  count
}

///|
fn pow_int(base : Int32, exp : Int32) -> Int32 {
  let mut p = 1
  for _ in 0..<exp {
    p = p * base
  }
  p
}

///|
fn decode_word(code : Int32, len : Int32, r : Int32) -> Array[Int32] {
  let w : Array[Int32] = []
  let mut x = code
  for _ in 0..<len {
    w.push(x % r + 1)
    x = x / r
  }
  w
}

///|
fn word_surjective(w : Array[Int32], r : Int32) -> Bool {
  let seen : Array[Bool] = []
  for _ in 0..<r {
    seen.push(false)
  }
  for a in w {
    if a >= 1 && a <= r {
      seen[a - 1] = true
    }
  }
  let mut ok = true
  for b in seen {
    if !b {
      ok = false
    }
  }
  ok
}

///|
fn word_nondegenerate(w : Array[Int32]) -> Bool {
  let mut ok = true
  for i in 1..<w.length() {
    if w[i] == w[i - 1] {
      ok = false
    }
  }
  ok
}

///|
/// All degree-`d` generators of the arity-`r` component.
pub fn e_words(r : Int32, d : Int32) -> Array[Array[Int32]] {
  let len = r + d
  let total = pow_int(r, len)
  let out : Array[Array[Int32]] = []
  for code in 0..<total {
    let w = decode_word(code, len, r)
    if word_surjective(w, r) && word_nondegenerate(w) {
      out.push(w)
    }
  }
  out
}

///|
fn word_code(w : Array[Int32], r : Int32) -> Int32 {
  let mut code = 0
  let mut p = 1
  for a in w {
    code = code + (a - 1) * p
    p = p * r
  }
  code
}

///|
/// The arity-`r` chain complex of the surjection operad, truncated at degree
/// `maxdeg`.  The differential deletes one entry at a time; a deletion that
/// destroys surjectivity or non-degeneracy contributes zero.
pub fn e_complex(r : Int32, maxdeg : Int32) -> ChainComplex {
  let dims : Array[Int32] = []
  let words : Array[Array[Array[Int32]]] = []
  for d in 0..<=maxdeg {
    let ws = e_words(r, d)
    dims.push(ws.length())
    words.push(ws)
  }
  let boundaries : Array[Array[Bits]] = []
  boundaries.push([])
  for d in 1..<=maxdeg {
    let cols : Array[Bits] = []
    let cur = words[d]
    let prev = words[d - 1]
    // dense code -> index table for the previous degree
    let table : Array[Int32] = []
    let table_size = pow_int(r, r + d - 1)
    for _ in 0..<table_size {
      table.push(-1)
    }
    for i in 0..<prev.length() {
      table[word_code(prev[i], r)] = i
    }
    for w in cur {
      let col = Bits::new(dims[d - 1])
      for i in 0..<w.length() {
        let face : Array[Int32] = []
        for j in 0..<w.length() {
          if j != i {
            face.push(w[j])
          }
        }
        if word_surjective(face, r) && word_nondegenerate(face) {
          let idx = table[word_code(face, r)]
          if idx >= 0 {
            col.flip(idx)
          }
        }
      }
      cols.push(col)
    }
    boundaries.push(cols)
  }
  ChainComplex::new(dims, boundaries)
}

///|
/// Homology of the arity-`r` surjection component.  Contractibility means
/// `E(r)_0 = F_2` and `E(r)_d = 0` for `d > 0` (for `r >= 1`).
pub fn e_betti(r : Int32, maxdeg : Int32) -> Array[Int32] {
  let full = e_complex(r, maxdeg + 1).betti()
  let out : Array[Int32] = []
  for d in 0..<=maxdeg {
    out.push(full[d])
  }
  out
}

///|
/// Dimensions of the free `E_∞`-algebra on `g` generators of degree 0,
/// degree by degree: the number of monomials of degree `d` is
/// `C(d+g-1, g-1)`.  This is the underlying commutative algebra; the
/// `E_∞` structure adds Dyer–Lashof operations but no new additive basis.
pub fn free_einfty_dims(g : Int32, maxdeg : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for d in 0..<=maxdeg {
    let mut num = 1
    for i in 0..<(g - 1) {
      num = num * (d + g - 1 - i)
    }
    let mut den = 1
    for i in 1..<=(g - 1) {
      den = den * i
    }
    out.push(num / den)
  }
  out
}

///|
/// Partition numbers `p(0), ..., p(n)`: dimensions of the free `E_∞`-algebra
/// on one degree-0 generator (equivalently, of the polynomial ring `F_2[x]`).
pub fn partition_numbers(n : Int32) -> Array[Int32] {
  let dp : Array[Int32] = []
  for _ in 0..<=n {
    dp.push(0)
  }
  dp[0] = 1
  for part in 1..<=n {
    for total in part..<=n {
      dp[total] = dp[total] + dp[total - part]
    }
  }
  dp
}
