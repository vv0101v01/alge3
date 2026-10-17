///|
test "A-infinity axioms on examples" {
  let ext = exterior_algebra()
  assert_true(ext.check_all())
  let dga = line_dga()
  assert_true(dga.check_m1sq())
  assert_true(dga.check_derivation())
  assert_true(dga.check_all())
  let poly = truncated_polynomial()
  assert_true(poly.check_all())
}

///|
test "surjection operad components are contractible" {
  assert_eq(e_betti(2, 4), [1, 0, 0, 0, 0])
  assert_eq(e_betti(3, 3), [1, 0, 0, 0])
  assert_eq(e_betti(4, 2), [1, 0, 0])
  assert_true(e_complex(3, 3).check_d2())
}

///|
test "free E-infinity dimensions" {
  assert_eq(free_einfty_dims(1, 6), [1, 1, 1, 1, 1, 1, 1])
  assert_eq(free_einfty_dims(2, 4), [1, 2, 3, 4, 5])
  assert_eq(free_einfty_dims(3, 3), [1, 3, 6, 10])
  assert_eq(partition_numbers(6), [1, 1, 2, 3, 5, 7, 11])
}
