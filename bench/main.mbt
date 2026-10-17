///|
using @core {type Bits, type BoolMat}

///|
fn lcg_next(s : Array[UInt64]) -> UInt64 {
  s[0] = s[0] * 6364136223846793005UL + 1442695040888963407UL
  s[0]
}

///|
fn random_bool_mat(m : Int32, n : Int32, seed : UInt64) -> BoolMat {
  let s = [seed]
  let rows : Array[Bits] = []
  for _ in 0..<m {
    let r = Bits::new(n)
    for j in 0..<n {
      if lcg_next(s) >> 63 == 1UL {
        r.set(j)
      }
    }
    rows.push(r)
  }
  BoolMat::new(rows, n)
}

///|
fn dense_of(m : BoolMat) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for i in 0..<m.nrows() {
    let row : Array[Int32] = []
    for j in 0..<m.ncols {
      row.push(if m.get(i, j) { 1 } else { 0 })
    }
    out.push(row)
  }
  out
}

///|
/// Scalar Gaussian elimination over GF(2), the baseline for the bit-parallel
/// `rank`.
fn rank_scalar(rows : Array[Array[Int32]], ncols : Int32) -> Int32 {
  let a : Array[Array[Int32]] = []
  for row in rows {
    let r : Array[Int32] = []
    for x in row {
      r.push(x)
    }
    a.push(r)
  }
  let m = a.length()
  let mut rank = 0
  for c in 0..<ncols {
    let mut piv = -1
    for i in rank..<m {
      if a[i][c] == 1 && piv < 0 {
        piv = i
      }
    }
    if piv >= 0 {
      let tmp = a[rank]
      a[rank] = a[piv]
      a[piv] = tmp
      for i in 0..<m {
        if i != rank && a[i][c] == 1 {
          for j in c..<ncols {
            a[i][j] = a[i][j] ^ a[rank][j]
          }
        }
      }
      rank = rank + 1
    }
  }
  rank
}

///|
fn prop_matrix(n : Int32) -> Array[Array[Int32]] {
  let sz = 2 * n
  let out : Array[Array[Int32]] = []
  for i in 0..<sz {
    let row : Array[Int32] = []
    for j in 0..<sz {
      if i == j {
        row.push(0)
      } else {
        row.push((i * 3 + j * 5 + 1) % 1009)
      }
    }
    out.push(row)
  }
  out
}

///|
fn time_us(f : () -> Unit, reps : Int32) -> Double {
  // warm up
  f()
  let t0 = @cbench.monotonic_clock_start()
  for _ in 0..<reps {
    f()
  }
  let dt = @cbench.monotonic_clock_end(t0)
  dt / reps.to_double()
}

///|
fn main {
  println("MoonBit derived-mathematics benchmark")
  println("toolchain: moonc v0.10.15, target native")
  let sink = [0]

  // 1. Rank over GF(2): bit-parallel vs scalar.
  let m512 = random_bool_mat(512, 512, 20261017UL)
  let d512 = dense_of(m512)
  let s1 = time_us(() => sink[0] = sink[0] + @core.rank_mat(m512), 5)
  let s2 = time_us(() => sink[0] = sink[0] + rank_scalar(d512, 512), 5)
  println("rank 512x512 us: bitset \{s1}, scalar \{s2}, speedup \{s2 / s1}")

  // 2. Boolean matrix multiplication.
  let a = random_bool_mat(256, 256, 7UL)
  let b = random_bool_mat(256, 256, 11UL)
  let a_dense = dense_of(a)
  let b_dense = dense_of(b)
  let s3 = time_us(
    () => {
      let c = a.mul_or(b)
      sink[0] = sink[0] + (if c.get(0, 0) { 1 } else { 0 })
    },
    5,
  )
  let s4 = time_us(
    () => {
      let c : Array[Array[Int32]] = []
      for i in 0..<256 {
        let row : Array[Int32] = []
        for j in 0..<256 {
          let mut v = 0
          for t in 0..<256 {
            v = v | (a_dense[i][t] & b_dense[t][j])
          }
          row.push(v)
        }
        c.push(row)
      }
      sink[0] = sink[0] + c[0][0]
    },
    5,
  )
  println("matmul 256 us: bitset \{s3}, scalar \{s4}, speedup \{s4 / s3}")

  // 3. Bar construction.
  let s5 = time_us(
    () => {
      sink[0] = sink[0] + @homotopy.bar_betti(@homotopy.cyclic_group(2), 8)[8]
    },
    5,
  )
  println("bar construction BZ/2 degree 8 us: \{s5}")

  // 4. Surjection operad.
  let s6 = time_us(
    () => {
      let bb = @algebra.e_betti(4, 3)
      sink[0] = sink[0] + bb[0]
    },
    5,
  )
  println("surjection operad E(4) through degree 3 us: \{s6}")

  // 5. Wick theorem: DP vs brute.
  let n = 8
  let pr = prop_matrix(n)
  let verts : Array[Int32] = []
  for i in 0..<(2 * n) {
    verts.push(i)
  }
  let s7 = time_us(() => sink[0] = sink[0] + @algebra.wick_dp(n, pr, 1009), 5)
  let s8 = time_us(
    () => sink[0] = sink[0] + @algebra.wick_brute(verts, pr, 1009),
    5,
  )
  println("Wick 16-point us: DP \{s7}, brute \{s8}, speedup \{s8 / s7}")

  // 6. Derived singularity invariants.
  let e8 = @derived.poly_of([([3, 0], 1), ([0, 5], 1)])
  let s9 = time_us(
    () => sink[0] = sink[0] + @derived.milnor_number(e8, [5, 3], 1009, 30),
    5,
  )
  println("Milnor number E8 us: \{s9}")

  // 7. Heisenberg commutator check.
  let s10 = time_us(
    () => {
      sink[0] = sink[0] +
        (if @algebra.check_heisenberg_commutator(8, 2, 1009) { 1 } else { 0 })
    },
    5,
  )
  println("Heisenberg commutator check us: \{s10}")

  println("checksum \{sink[0]}")

  // Mathematical summary (not timed).
  println("")
  println(@homotopy.complex_summary("S^2", @homotopy.sphere()))
  println(@homotopy.complex_summary("T^2", @homotopy.torus()))
  println(@homotopy.complex_summary("RP^2", @homotopy.projective_plane()))
  println(@homotopy.complex_summary("Mobius", @homotopy.mobius_band()))
  println("BZ/2 betti: [1, 1, 1, 1, 1]")
  let z2 = @homotopy.bar_betti(@homotopy.cyclic_group(2), 7)
  println("bar Z/2 through 7: \{@core.ints_to_s(z2)}")
  let e4 = @algebra.e_betti(4, 3)
  println("E(4) betti: \{@core.ints_to_s(e4)}")
  let ext = @algebra.exterior_algebra()
  println("A-infinity exterior algebra OK: \{ext.check_all()}")
  let dga = @algebra.line_dga()
  println("A-infinity line dga OK: \{dga.check_all()}")
  println(
    "Heisenberg character p(0..8): \{@core.ints_to_s(@algebra.heisenberg_character(8))}",
  )
  let mu_a2 = @derived.milnor_number(
    @derived.poly_of([([3, 0], 1), ([0, 2], 1)]),
    [2, 3],
    1009,
    12,
  )
  println("Milnor A2: \{mu_a2}")
  let mu_e8 = @derived.milnor_number(e8, [5, 3], 1009, 30)
  println("Milnor E8: \{mu_e8}")
  let tau_e7 = @derived.tjurina_number(
    @derived.poly_of([([3, 0], 1), ([1, 3], 1)]),
    [3, 2],
    1009,
    18,
  )
  println("Tjurina E7: \{tau_e7}")
  let rep : @derived.QRep = @derived.QRep::new(2, [1, 1], [
    @derived.arrow(0, 1, [[1]]),
    @derived.arrow(0, 1, [[1]]),
  ])
  let (ext0, ext1) = rep.ext01()
  println("Kronecker Ext^0, Ext^1: \{ext0}, \{ext1}")
}
