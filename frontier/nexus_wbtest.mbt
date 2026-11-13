///|
test "nexus: stable spectral fast leaf FFT" {
  assert_true(check_stable_spectral_fft())
  assert_eq(nx_butterfly_op_count(16), 32)
  let a = ntt_butterfly([1, 2, 3, 4], false)
  assert_eq(ntt_butterfly(a, true), [1, 2, 3, 4])
  assert_eq(ntt_recursive([1, 2, 3, 4]), ntt_naive([1, 2, 3, 4]))
}

///|
test "nexus: cyclic butterfly FFT" {
  assert_true(check_cyclic_butterfly_fft())
  assert_eq(
    nx_cyclic_convolve([1, 0, 0, 0, 0, 0, 0, 0], [5, 6, 7, 8, 9, 10, 11, 12]),
    [5, 6, 7, 8, 9, 10, 11, 12],
  )
}

///|
test "nexus: homotopy loop space mod-cut bijection" {
  assert_true(check_loop_space_bijection())
}

///|
test "nexus: Einstein boost category over F13" {
  assert_true(check_einstein_boost_category())
}

///|
test "nexus: lattice reconstruction (Birkhoff)" {
  assert_true(check_lattice_reconstruction())
}

///|
test "nexus: dual / Riemannian / super hypercube" {
  assert_true(check_dual_riemann_super_hypercube())
}

///|
test "nexus: stable spin operator (double cover)" {
  assert_true(check_stable_spin_operator())
}

///|
test "nexus: recursive tree geometry and fold homomorphism" {
  assert_true(check_recursive_tree_geometry())
  assert_eq(nx_tree_dist(0, 7), 6)
  assert_eq(nx_tree_dist(0, 1), 2)
}

///|
test "nexus: total mappings converge, fiber partitions" {
  assert_true(check_homotopy_convergence_maps())
}

///|
test "nexus: line bundles over C4 classified by monodromy" {
  assert_true(check_vector_bundle_category())
  assert_eq(nx_monodromy([2, 2, 2, 2]), 1)
}

///|
test "nexus: knot determinants and Alexander data" {
  assert_true(check_knot_geometry_homology())
  assert_eq(nx_knot_determinant(0), 1)
  assert_eq(nx_knot_determinant(1), 3)
  assert_eq(nx_knot_determinant(2), 5)
}
