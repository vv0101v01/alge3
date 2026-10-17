///|
test "Heisenberg commutators" {
  assert_true(check_heisenberg_commutator(6, 1, 1009))
  assert_true(check_heisenberg_commutator(6, 2, 1009))
}

///|
test "Wick theorem DP equals brute force" {
  let n = 5
  let prop : Array[Array[Int32]] = []
  for i in 0..<(2 * n) {
    let row : Array[Int32] = []
    for j in 0..<(2 * n) {
      if i < j {
        row.push((i + j + 1) % 7)
      } else if i > j {
        row.push((i + j + 1) % 7)
      } else {
        row.push(0)
      }
    }
    prop.push(row)
  }
  let verts : Array[Int32] = []
  for i in 0..<(2 * n) {
    verts.push(i)
  }
  assert_eq(wick_dp(n, prop, 1009), wick_brute(verts, prop, 1009))
}

///|
test "character coefficients are partition numbers" {
  assert_eq(heisenberg_character(6), [1, 1, 2, 3, 5, 7, 11])
}

///|
test "rank varieties of exterior modules" {
  let reg = regular_ext_module(2)
  let (mr, count) = rank_variety_stats(reg, 2)
  assert_eq(mr, 2)
  assert_eq(count, 1) // only t = 0 has rank below the maximum
  let triv = trivial_ext_module(2)
  let (mr2, count2) = rank_variety_stats(triv, 2)
  assert_eq(mr2, 0)
  assert_eq(count2, 0) // constant rank: no point lies below the maximum
}
