///|
/// Finite truncation of the rank-one Heisenberg Fock space: states are
/// multiplicity vectors `(m_1, m_2, ..., m_N)` with `sum k*m_k <= N`,
/// representing `prod_k (alpha_{-k})^{m_k} |0>`.
pub fn fock_states(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let cur : Array[Int32] = []
  for _ in 0..<=n {
    cur.push(0)
  }
  gen_states(1, n, cur, out, n)
  out
}

///|
fn gen_states(
  part : Int32,
  remaining : Int32,
  cur : Array[Int32],
  out : Array[Array[Int32]],
  n : Int32,
) -> Unit {
  if part > n {
    let st : Array[Int32] = []
    for x in cur {
      st.push(x)
    }
    out.push(st)
  } else {
    let maxk = remaining / part
    for k in 0..<=maxk {
      cur[part] = k
      gen_states(part + 1, remaining - k * part, cur, out, n)
    }
    cur[part] = 0
  }
}

///|
fn state_total(s : Array[Int32]) -> Int32 {
  let mut t = 0
  for k in 1..<s.length() {
    t = t + k * s[k]
  }
  t
}

///|
fn state_index(states : Array[Array[Int32]], s : Array[Int32]) -> Int32 {
  let mut ans = -1
  for i in 0..<states.length() {
    let t = states[i]
    let mut same = true
    for j in 0..<s.length() {
      if t[j] != s[j] {
        same = false
      }
    }
    if same {
      ans = i
    }
  }
  ans
}

///|
/// Matrix of the mode `alpha_m` on the truncated Fock space, over `F_p`.
/// For `m > 0`, `alpha_m = m * d/dp_m`: it removes one part `m` with
/// coefficient `m * multiplicity`.  For `m < 0`, `alpha_m` multiplies by
/// `p_{|m|}`, i.e. adds the part `|m|`.
pub fn heisenberg_matrix(
  n : Int32,
  m : Int32,
  p : Int32,
) -> Array[Array[Int32]] {
  let states = fock_states(n)
  let d = states.length()
  let mat : Array[Array[Int32]] = []
  for _ in 0..<d {
    let row : Array[Int32] = []
    for _ in 0..<d {
      row.push(0)
    }
    mat.push(row)
  }
  for i in 0..<d {
    let s = states[i]
    if m < 0 {
      let k = -m
      if state_total(s) + k <= n {
        let t : Array[Int32] = []
        for j in 0..<s.length() {
          t.push(s[j])
        }
        t[k] = t[k] + 1
        let j = state_index(states, t)
        if j >= 0 {
          mat[j][i] = 1
        }
      }
    } else if m > 0 {
      if s[m] > 0 {
        let t : Array[Int32] = []
        for j in 0..<s.length() {
          t.push(s[j])
        }
        t[m] = t[m] - 1
        let j = state_index(states, t)
        if j >= 0 {
          mat[j][i] = @core.fp_norm(m * s[m], p)
        }
      }
    }
  }
  mat
}

///|
fn mat_mul_fp(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
  p : Int32,
) -> Array[Array[Int32]] {
  let n = a.length()
  let k = b.length()
  let m = if k == 0 { 0 } else { b[0].length() }
  let c : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<m {
      let mut s = 0
      for t in 0..<k {
        s = s + a[i][t] * b[t][j]
      }
      row.push(@core.fp_norm(s, p))
    }
    c.push(row)
  }
  c
}

///|
fn mat_sub_fp(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
  p : Int32,
) -> Array[Array[Int32]] {
  let n = a.length()
  let m = if n == 0 { 0 } else { a[0].length() }
  let c : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<m {
      row.push(@core.fp_sub(a[i][j], b[i][j], p))
    }
    c.push(row)
  }
  c
}

///|
/// Verify `[alpha_m, alpha_{-n}] = m * delta_{m,n} * Id` on all states with
/// enough room for the raising operator.  This is the Heisenberg algebra
/// relation `[alpha_m, alpha_n] = m delta_{m+n,0}`.
pub fn check_heisenberg_commutator(n : Int32, m : Int32, p : Int32) -> Bool {
  let states = fock_states(n)
  let d = states.length()
  let ap = heisenberg_matrix(n, m, p)
  let am = heisenberg_matrix(n, -m, p)
  let aamp = mat_mul_fp(ap, am, p)
  let amap = mat_mul_fp(am, ap, p)
  let com = mat_sub_fp(aamp, amap, p)
  let mut ok = true
  for i in 0..<d {
    for j in 0..<d {
      // On a truncated Fock space the relation only holds on the subspace
      // of states with room for alpha_{-m}; compare that stable submatrix.
      if state_total(states[i]) + m <= n && state_total(states[j]) + m <= n {
        let expect = if i == j { @core.fp_norm(m, p) } else { 0 }
        if com[i][j] != expect {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// Wick's theorem as a subset DP: sum over all perfect matchings of the
/// `2n`-point function, where `prop[i][j]` is the propagator between `i`
/// and `j`.  The naive enumeration of pairings costs `(2n-1)!!`; the DP costs
/// `O(n^2 2^{2n})` and is faster from `2n = 12` onwards.
pub fn wick_dp(n : Int32, prop : Array[Array[Int32]], p : Int32) -> Int32 {
  let sz = 1 << (2 * n)
  let dp : Array[Int32] = []
  for _ in 0..<sz {
    dp.push(0)
  }
  dp[0] = 1
  for mask in 1..<sz {
    // lowest set bit i
    let i = @core.trailing_zeros64(mask.to_uint64())
    let rest = mask ^ (1 << i)
    let mut s = 0
    for j in 0..<(2 * n) {
      if j != i && (rest & (1 << j)) != 0 {
        s = s + prop[i][j] * dp[rest ^ (1 << j)]
      }
    }
    dp[mask] = @core.fp_norm(s, p)
  }
  dp[sz - 1]
}

///|
/// Naive recursive evaluation of Wick's theorem, used as a correctness
/// oracle for `wick_dp`.
pub fn wick_brute(
  verts : Array[Int32],
  prop : Array[Array[Int32]],
  p : Int32,
) -> Int32 {
  if verts.length() == 0 {
    1
  } else {
    let i = verts[0]
    let rest : Array[Int32] = []
    for k in 1..<verts.length() {
      rest.push(verts[k])
    }
    let mut s = 0
    for jj in 0..<rest.length() {
      let j = rest[jj]
      let sub : Array[Int32] = []
      for k in 0..<rest.length() {
        if k != jj {
          sub.push(rest[k])
        }
      }
      s = s + prop[i][j] * wick_brute(sub, prop, p)
    }
    @core.fp_norm(s, p)
  }
}

///|
/// Coefficients of the vacuum character of the rank-one Heisenberg VOA:
/// `chi(q) = q^{-1/24} / prod_{n>=1}(1-q^n)`, so the coefficient of
/// `q^{n-1/24}` is the partition number `p(n)`.
pub fn heisenberg_character(n : Int32) -> Array[Int32] {
  partition_numbers(n)
}

///|
/// A finite module over the exterior algebra `Λ(x_1,...,x_n)`, encoded by
/// the matrices of multiplication by each generator.  Over `F_p` this is the
/// input for the rank-variety computation.
pub struct ExtModule {
  n : Int32
  dim : Int32
  gens : Array[Array[Array[Int32]]]
}

///|
/// Trivial module: all generators act by zero; the rank variety is the whole
/// affine space `A^n`.
pub fn trivial_ext_module(n : Int32) -> ExtModule {
  let gens : Array[Array[Array[Int32]]] = []
  for _ in 0..<n {
    let m : Array[Array[Int32]] = []
    for _ in 0..<1 {
      m.push([0])
    }
    gens.push(m)
  }
  ExtModule::{ n, dim: 1, gens, }
}

///|
/// Regular module `Λ` itself, with `x_i` acting by left multiplication
/// (over `F_2`, so no signs).  Basis: subsets of `{0,...,n-1}` encoded by
/// bitmasks.
pub fn regular_ext_module(n : Int32) -> ExtModule {
  let dim = 1 << n
  let gens : Array[Array[Array[Int32]]] = []
  for i in 0..<n {
    let m : Array[Array[Int32]] = []
    for _ in 0..<dim {
      let row : Array[Int32] = []
      for _ in 0..<dim {
        row.push(0)
      }
      m.push(row)
    }
    for s in 0..<dim {
      if (s & (1 << i)) == 0 {
        m[s | (1 << i)][s] = 1
      }
    }
    gens.push(m)
  }
  ExtModule::{ n, dim, gens, }
}

///|
/// Rank of the generic element `sum t_i x_i` for every `t in F_p^n`.
/// Returns `(max_rank, number_of_t_with_rank_lt_max)`; the latter is the
/// number of field points of the rank variety.
pub fn rank_variety_stats(m : ExtModule, p : Int32) -> (Int32, Int32) {
  let total = pow_int_local(p, m.n)
  let mut maxrank = 0
  let ranks : Array[Int32] = []
  for code in 0..<total {
    let mat : Array[Array[Int32]] = []
    for _ in 0..<m.dim {
      let row : Array[Int32] = []
      for _ in 0..<m.dim {
        row.push(0)
      }
      mat.push(row)
    }
    let mut x = code
    for i in 0..<m.n {
      let t = x % p
      x = x / p
      if t != 0 {
        for a in 0..<m.dim {
          for b in 0..<m.dim {
            mat[a][b] = @core.fp_norm(mat[a][b] + t * m.gens[i][a][b], p)
          }
        }
      }
    }
    let r = @core.fp_rank(mat, p)
    ranks.push(r)
    if r > maxrank {
      maxrank = r
    }
  }
  let mut count = 0
  for r in ranks {
    if r < maxrank {
      count = count + 1
    }
  }
  (maxrank, count)
}

///|
fn pow_int_local(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<exp {
    r = r * base
  }
  r
}
