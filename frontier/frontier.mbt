///|
using @cubical {type Cof}

///|
using @face_bdd {type Dim, type Face}

///|
using @finite {type Term}

///|
// Frontier layer: finite, decidable models of
//   * the De Morgan cubical algebra and small cubical operators,
//   * rewriting decidability / confluence for dimension terms,
//   * local complementedness of path types,
//   * deformation functors and their moduli (truncation) tower,
//   * derived fiber products of finite chain complexes,
//   * discrete connections, curvature, and horizontal distributions,
//   * universal coverings of finite graphs,
//   * geometric higher-groupoid models (fundamental groupoids of
//     the circle and the torus, decided by covering lifts),
//   * weak omega-groupoids (skeletal categorical groups with a
//     carry 3-cocycle associator),
//   * adjoint logic (Heyting and quantifier adjunctions on finite
//     powerset lattices),
//   * symbolic dynamic execution integrated with NbE,
//   * hypercubes in 3D: A-infinity top boundary, cyclic homology,
//     fiber integration, and univalence shadow transport,
//   * the spectral nexus: butterfly NTT spectra, loop spaces,
//     Einstein boosts, lattice reconstruction, dual/Riemannian
//     hypercubes, spin rotors, recursive trees, total mappings,
//     line bundles over a cycle, and knot determinants.
//
// Every statement is checked exhaustively in its finite model, in
// the style of the layers below.  `verify_frontier_suite` runs all
// of them and reports per-topic results.

///|
/// Per-topic verification results of the frontier layer.
#derive(Debug, Eq)
pub(all) struct FrontierReport {
  de_morgan_ok : Bool
  small_cubical_operators_ok : Bool
  confluence_decidability_ok : Bool
  path_locally_complemented_ok : Bool
  deformation_moduli_ok : Bool
  derived_fiber_product_ok : Bool
  connection_curvature_ok : Bool
  universal_covering_ok : Bool
  higher_groupoid_ok : Bool
  weak_omega_groupoid_ok : Bool
  adjoint_logic_ok : Bool
  symbolic_nbe_ok : Bool
  hypercube3d_ok : Bool
  hypercube_solid_betti : Array[Int32]
  hypercube_boundary_betti : Array[Int32]
  hypercube_cyclic_betti_low : Array[Int32]
  hypercube_projected_boundary_facets : Int32
  spectral_nexus_ok : Bool
  butterfly_ops_16 : Int32
  bundle_iso_classes : Int32
  trefoil_determinant : Int32
  derived_pullback_betti : Array[Int32]
  plaquette_holonomy : Array[Int32]
  complemented_subobject_count : Int32
}

///|
pub extend FrontierReport with @debug.Debug::{to_repr}

///|
pub extend FrontierReport with Eq::{not_equal, equal}

///|
/// Run every frontier verification and collect the report.
pub fn verify_frontier_suite() -> FrontierReport {
  FrontierReport::{
    de_morgan_ok: check_de_morgan_cubical_algebra(),
    small_cubical_operators_ok: check_small_cubical_operators(),
    confluence_decidability_ok: check_confluence_decidability(),
    path_locally_complemented_ok: check_path_locally_complemented(),
    deformation_moduli_ok: check_deformation_moduli(),
    derived_fiber_product_ok: check_derived_fiber_product(),
    connection_curvature_ok: check_connection_curvature(),
    universal_covering_ok: check_universal_covering(),
    higher_groupoid_ok: check_higher_groupoid_model(),
    weak_omega_groupoid_ok: check_weak_omega_groupoid(),
    adjoint_logic_ok: check_adjoint_logic(),
    symbolic_nbe_ok: check_symbolic_nbe(),
    hypercube3d_ok: check_hypercube3d(),
    hypercube_solid_betti: hc_solid_betti(5),
    hypercube_boundary_betti: hc_boundary_betti(5),
    hypercube_cyclic_betti_low: hc_cyclic_betti_low(5),
    hypercube_projected_boundary_facets: hc_projected_top_boundary(5).length(),
    spectral_nexus_ok: check_spectral_nexus_all(),
    butterfly_ops_16: nx_butterfly_op_count(16),
    bundle_iso_classes: nx_bundle_iso_class_count(),
    trefoil_determinant: nx_knot_determinant(1),
    derived_pullback_betti: derived_pullback_example_betti(),
    plaquette_holonomy: magnetic_plaquette_holonomy(),
    complemented_subobject_count: complemented_subobject_count(),
  }
}

///|
pub fn FrontierReport::all_ok(self : FrontierReport) -> Bool {
  self.de_morgan_ok &&
  self.small_cubical_operators_ok &&
  self.confluence_decidability_ok &&
  self.path_locally_complemented_ok &&
  self.deformation_moduli_ok &&
  self.derived_fiber_product_ok &&
  self.connection_curvature_ok &&
  self.universal_covering_ok &&
  self.higher_groupoid_ok &&
  self.weak_omega_groupoid_ok &&
  self.adjoint_logic_ok &&
  self.symbolic_nbe_ok &&
  self.hypercube3d_ok &&
  self.spectral_nexus_ok
}

///|
/// All frontier verifications as a single boolean.
pub fn check_frontier_all() -> Bool {
  verify_frontier_suite().all_ok()
}
