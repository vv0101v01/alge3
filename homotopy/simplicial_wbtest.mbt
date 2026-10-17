///|
test "circle and sphere homology" {
  let c = circle()
  assert_eq(c.count(0), 3)
  assert_eq(c.count(1), 3)
  assert_eq(c.betti(), [1, 1])
  let s = sphere()
  assert_eq(s.count(2), 4)
  assert_eq(s.betti(), [1, 0, 1])
  assert_eq(s.euler(), 2)
}

///|
test "torus homology" {
  let t = torus()
  assert_eq(t.count(0), 9)
  assert_eq(t.count(1), 27)
  assert_eq(t.count(2), 18)
  assert_eq(t.euler(), 0)
  assert_eq(t.betti(), [1, 2, 1])
}

///|
test "projective plane over F2" {
  let rp = projective_plane()
  assert_eq(rp.count(0), 6)
  assert_eq(rp.count(1), 15)
  assert_eq(rp.count(2), 10)
  assert_eq(rp.euler(), 1)
  assert_eq(rp.betti(), [1, 1, 1])
}

///|
test "mobius band" {
  let m = mobius_band()
  assert_eq(m.count(2), 9)
  assert_eq(m.euler(), 0)
  assert_eq(m.betti(), [1, 1, 0])
}

///|
test "inner horn filling" {
  let d3 = simplex3()
  assert_true(fills_inner_horns_3(d3))
  let boundary = sphere()
  assert_false(fills_inner_horns_3(boundary))
}
