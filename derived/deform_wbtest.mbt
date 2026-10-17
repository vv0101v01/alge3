///|
test "Milnor numbers of ADE singularities" {
  let p = 1009
  // A_1: x^2 + y^2
  let a1 = poly_of([([2, 0], 1), ([0, 2], 1)])
  assert_eq(milnor_number(a1, [1, 1], p, 8), 1)
  // A_2: x^3 + y^2, weights (2,3), degree 6
  let a2 = poly_of([([3, 0], 1), ([0, 2], 1)])
  assert_eq(milnor_number(a2, [2, 3], p, 12), 2)
  // A_4: x^5 + y^2, weights (2,5)
  let a4 = poly_of([([5, 0], 1), ([0, 2], 1)])
  assert_eq(milnor_number(a4, [2, 5], p, 20), 4)
  // E_6: x^3 + y^4, weights (4,3), degree 12
  let e6 = poly_of([([3, 0], 1), ([0, 4], 1)])
  assert_eq(milnor_number(e6, [4, 3], p, 24), 6)
  // E_8: x^3 + y^5, weights (5,3), degree 15
  let e8 = poly_of([([3, 0], 1), ([0, 5], 1)])
  assert_eq(milnor_number(e8, [5, 3], p, 30), 8)
}

///|
test "Tjurina equals Milnor for quasi-homogeneous singularities" {
  let p = 1009
  let e7 = poly_of([([3, 0], 1), ([1, 3], 1)])
  assert_eq(milnor_number(e7, [3, 2], p, 18), 7)
  assert_eq(tjurina_number(e7, [3, 2], p, 18), 7)
}

///|
test "Hilbert function of A_2 Jacobian algebra" {
  let p = 1009
  let a2 = poly_of([([3, 0], 1), ([0, 2], 1)])
  let h = quotient_hilbert(a2, [2, 3], p, 12, false)
  // quotient has basis 1 (weight 0) and x (weight 2)
  assert_eq(h[0], 1)
  assert_eq(h[2], 1)
}

///|
test "A1 and D4 Milnor numbers" {
  let p = 1009
  let a1 = poly_of([([2, 0], 1), ([0, 2], 1)])
  assert_eq(milnor_number(a1, [1, 1], p, 8), 1)
  let d4 = poly_of([([3, 0], 1), ([1, 2], 1)])
  assert_eq(milnor_number(d4, [2, 2], p, 12), 4)
}
