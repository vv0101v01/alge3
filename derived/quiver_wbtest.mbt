///|
test "Ext groups for A2 quivers" {
  let r = QRep::new(2, [1, 1], [arrow(0, 1, [[1]])])
  let (e0, e1) = r.ext01()
  assert_eq(e0, 1)
  assert_eq(e1, 0)
  let r2 = QRep::new(2, [1, 2], [arrow(0, 1, [[1], [0]])])
  let (f0, f1) = r2.ext01()
  assert_eq(f0, 3) // X1 scalar, X2 lower-triangular
  assert_eq(f1, 0)
}

///|
test "Ext groups for the Kronecker quiver" {
  // Two arrows 0 -> 1, dimension vector (1,1): Ext^1 has dimension 1.
  let r = QRep::new(2, [1, 1], [arrow(0, 1, [[1]]), arrow(0, 1, [[1]])])
  let (e0, e1) = r.ext01()
  assert_eq(e0, 1)
  assert_eq(e1, 1)
}

///|
test "Ext groups for A3 quiver" {
  let r = QRep::new(3, [1, 1, 1], [arrow(0, 1, [[1]]), arrow(1, 2, [[1]])])
  let (e0, e1) = r.ext01()
  assert_eq(e0, 1)
  assert_eq(e1, 0)
}
