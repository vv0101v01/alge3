///|
test "hypercube: face counts, solid and boundary homology" {
  assert_eq(hc_face_count(5, 0), 32)
  assert_eq(hc_face_count(5, 1), 80)
  assert_eq(hc_face_count(5, 5), 1)
  assert_eq(hc_solid_betti(4), [1, 0, 0, 0, 0])
  assert_eq(hc_boundary_betti(4), [1, 0, 0, 1])
  assert_eq(hc_boundary_betti(5), [1, 0, 0, 0, 1])
  assert_true(hc_solid_d2_ok(5))
  assert_true(hc_boundary_d2_ok(5))
}

///|
test "hypercube: A-infinity top boundary" {
  assert_true(hc_ainf_ok())
  // The top boundary has 2n facets and is a cycle, for n = 3, 4, 5.
  assert_eq(hc_top_facets(5).length(), 10)
  assert_true(hc_top_boundary_is_cycle(5))
  assert_true(hc_top_boundary_is_cycle(4))
}

///|
test "hypercube: small cubes subdivide the big cube, boundaries cancel inside" {
  assert_true(hc_subdivision_ok(3))
  assert_true(hc_subdivision_ok(4))
  assert_true(hc_subdivision_ok(5))
}

///|
test "hypercube: fiber integration sends the top boundary to the 3D top boundary" {
  assert_true(hc_fiber_integration_chain_map_ok(4))
  assert_true(hc_fiber_integration_chain_map_ok(5))
  assert_eq(hc_projected_top_boundary(5).length(), 6)
  assert_true(hc_projected_top_boundary_ok(5))
}

///|
test "hypercube: cyclic homology of the cyclic cubical model" {
  assert_true(hc_top_boundary_cyclic_ok(5))
  assert_true(hc_cyclic_d2_ok(4, 4))
  assert_true(hc_cyclic_d2_ok(5, 4))
  assert_eq(hc_cyclic_betti_low(3).length(), 4)
  assert_eq(hc_cyclic_betti_low(5), [1, 0, 0, 0])
  assert_eq(hc_cyclic_betti_low(3), [1, 0, 1, 0])
  assert_eq(hc_cyclic_betti_low(4), [1, 1, 1, 2])
}

///|
test "hypercube: univalence shadow transport computes" {
  assert_true(hc_univalence_shadow_ok())
  let e = hc_facet_shadow_iso()
  assert_true(@cubical.check_ua_beta(e))
  assert_eq(e.apply(1), 2)
  assert_eq(e.apply(3), 1)
}

///|
test "hypercube: vertex fibers and the 3D camera" {
  assert_true(hc_vertex_fibers_ok(5))
  assert_eq(hc_vertex_shadow(5, 31), 7)
  assert_true(hc_camera_ok(5))
}

///|
test "hypercube: full pipeline" {
  assert_true(check_hypercube3d())
}
