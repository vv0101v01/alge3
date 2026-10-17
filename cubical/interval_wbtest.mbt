///|
test "interval: dimension terms form a De Morgan algebra, decided by DNF" {
  let i = DVar(0)
  let j = DVar(1)
  let k = DVar(2)
  // De Morgan laws
  assert_true(dim_eq(DNot(DAnd(i, j)), DOr(DNot(i), DNot(j))))
  assert_true(dim_eq(DNot(DOr(i, j)), DAnd(DNot(i), DNot(j))))
  // distributivity and absorption
  assert_true(dim_eq(DAnd(i, DOr(j, k)), DOr(DAnd(i, j), DAnd(i, k))))
  assert_true(dim_eq(DOr(i, DAnd(i, j)), i))
  assert_true(dim_eq(DNot(DNot(i)), i))
  assert_true(dim_eq(DAnd(i, DOne), i))
  assert_true(dim_eq(DOr(i, DZero), i))
  // the interval is not Boolean: i /\ ~i is not 0, i \/ ~i is not 1
  assert_false(dim_eq(DAnd(i, DNot(i)), DZero))
  assert_false(dim_eq(DOr(i, DNot(i)), DOne))
  // connections: i /\ j is forced to 0 on the face i = 0, free elsewhere
  assert_eq(DAnd(i, j).eval3([0, 2]), 0)
  assert_eq(DAnd(i, j).eval3([1, 2]), 2)
  assert_eq(DAnd(i, j).eval3([1, 1]), 1)
  assert_eq(DOr(i, j).eval3([1, 2]), 1)
  assert_eq(DNot(i).eval3([2]), 2)
}

///|
test "face lattice: cofibration extents, entailment, maximal faces" {
  // n = 1: subcubes are {0}, {1}, generic
  assert_eq(cof_extent_size(face_cof(0, 0), 1), 1)
  assert_eq(cof_extent_size(COr(face_cof(0, 0), face_cof(0, 1)), 1), 2)
  // (i=0) or (i=1) is not top: it misses the generic subcube
  assert_false(cof_is_top(COr(face_cof(0, 0), face_cof(0, 1)), 1))
  assert_true(cof_is_top(CTop, 1))
  assert_true(cof_is_bot(CBot, 2))
  // n = 2
  assert_eq(cof_extent_size(face_cof(0, 0), 2), 3)
  assert_eq(cof_extent_size(CAnd(face_cof(0, 0), face_cof(1, 1)), 2), 1)
  assert_true(
    cof_entails(CAnd(face_cof(0, 0), face_cof(1, 1)), face_cof(0, 0), 2),
  )
  assert_false(cof_entails(face_cof(0, 0), face_cof(1, 1), 2))
  // distributivity in the face lattice
  let lhs = CAnd(face_cof(0, 0), COr(face_cof(1, 0), face_cof(1, 1)))
  let rhs = COr(
    CAnd(face_cof(0, 0), face_cof(1, 0)),
    CAnd(face_cof(0, 0), face_cof(1, 1)),
  )
  assert_true(cof_equiv(lhs, rhs, 2))
  // equations between composite dimension terms: (i /\ j = 0) is (i=0) or (j=0)
  assert_true(
    cof_equiv(
      CEq(DAnd(DVar(0), DVar(1)), 0),
      COr(face_cof(0, 0), face_cof(1, 0)),
      2,
    ),
  )
  // (~i = 1) is (i = 0)
  assert_true(cof_equiv(CEq(DNot(DVar(0)), 1), face_cof(0, 0), 1))
  // maximal faces of a two-face cofibration
  assert_eq(
    cof_maximal_faces(COr(face_cof(0, 0), face_cof(1, 1)), 2).length(),
    2,
  )
  // subcube arithmetic
  assert_eq(pow3(3), 27)
  assert_eq(
    meet_cube(face_cube(2, 0, 0), face_cube(2, 1, 1), 2),
    subcube_code([0, 1]),
  )
  assert_eq(meet_cube(face_cube(2, 0, 0), face_cube(2, 0, 1), 2), -1)
  assert_true(is_subface(subcube_code([0, 1]), face_cube(2, 0, 0), 2))
  assert_false(is_subface(face_cube(2, 0, 0), subcube_code([0, 1]), 2))
}
