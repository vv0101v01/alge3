///|
test "frontier: De Morgan cubical algebra axioms" {
  assert_true(check_de_morgan_cubical_algebra())
  // The free De Morgan algebra is not Boolean, and the decision
  // procedure sees it.
  let i = Dim::DVar(0)
  assert_false(dm_decide_eq(Dim::DAnd(i, Dim::DNeg(i)), Dim::DZero))
  assert_true(
    dm_decide_eq(
      Dim::DNeg(Dim::DAnd(i, Dim::DVar(1))),
      Dim::DOr(Dim::DNeg(i), Dim::DNeg(Dim::DVar(1))),
    ),
  )
}

///|
test "frontier: small cubical operators satisfy the cubical identities" {
  assert_true(check_small_cubical_operators())
  // Degeneracy followed by either face is the identity, and a
  // connection merges coordinates as expected.
  let deg = sc_degen(2, 0, 0)
  assert_eq(sc_face(3, deg, 0, 0), Some(0))
  assert_eq(sc_face(3, deg, 0, 1), Some(0))
  assert_eq(sc_conn([1, 2, 0], 0, true), [2, 0])
  assert_eq(sc_conn([1, 2, 0], 0, false), [1, 0])
}

///|
test "frontier: dimension rewriting is decidable and confluent" {
  assert_true(check_confluence_decidability())
}

///|
test "frontier: path types are locally complemented, decidably" {
  assert_true(check_path_locally_complemented())
  assert_eq(complemented_subobject_count(), 4)
}

///|
test "frontier: deformation functor and moduli tower" {
  assert_true(check_deformation_moduli())
  let d = deform_extend(deform_zero(1, 3), 1, 2)
  assert_eq(d.level, 2)
  assert_true(deform_eq(deform_truncate(d, 1), deform_zero(1, 3)))
}

///|
test "frontier: derived fiber product" {
  assert_true(check_derived_fiber_product())
  assert_eq(derived_pullback_example_betti(), [0, 1])
}

///|
test "frontier: connection, curvature, horizontal distribution" {
  assert_true(check_connection_curvature())
  assert_eq(magnetic_plaquette_holonomy(), [1, 0])
}

///|
test "frontier: universal covering of the circle graph" {
  assert_true(check_universal_covering())
  assert_eq(cover_lift([1, 1, 1, 1, 1, 1]), [0, 1, 2, 3, 4, 5, 6])
}

///|
test "frontier: higher groupoid model from covering lifts" {
  assert_true(check_higher_groupoid_model())
}

///|
test "frontier: weak omega-groupoid with nontrivial associator" {
  assert_true(check_weak_omega_groupoid())
}

///|
test "frontier: adjoint logic on finite lattices" {
  assert_true(check_adjoint_logic())
}

///|
test "frontier: symbolic execution agrees with NbE" {
  assert_true(check_symbolic_nbe())
  let traces = sym_exec(Term::TmVar(0), 1)
  assert_eq(traces.length(), 2)
  assert_eq(traces[0].result, Term::TmBool(false))
  assert_eq(traces[1].result, Term::TmBool(true))
}

///|
test "frontier: full suite report" {
  assert_true(verify_frontier_suite().all_ok())
}
