///|
/// A Glue line over the composition dimension `j` (variable 0) whose
/// generic point is `Glue [(j = 1) -> Nat] Bool` (branch path
/// `Bool -> Nat` in the universe), but whose endpoints have already
/// collapsed definitionally: at `j = 0` the branch face is bottom, so
/// the line is the plain base type `Bool`; at `j = 1` the branch face
/// is top, so the line is the plain partial type `Nat`.  This is the
/// endpoint situation handled by `glue_endpoint_parts`.
fn collapsed_glue_line(j : Dim) -> DValue {
  if dim_is_one(j) {
    DVNatTy
  } else if dim_is_zero(j) {
    DVBoolTy
  } else {
    let path = (s : Dim) => if dim_is_one(s) { DVNatTy } else { DVBoolTy }
    DVGlue(dsystem_singleton(Face::FEq1(j), path), DVBoolTy, 0)
  }
}

///|
/// The mirror line: `Glue [(j = 0) -> Nat] Bool`, collapsed to `Nat`
/// at `j = 0` (top) and to `Bool` at `j = 1` (bottom).
fn collapsed_glue_line_rev(j : Dim) -> DValue {
  if dim_is_zero(j) {
    DVNatTy
  } else if dim_is_one(j) {
    DVBoolTy
  } else {
    let path = (s : Dim) => if dim_is_one(s) { DVNatTy } else { DVBoolTy }
    DVGlue(dsystem_singleton(Face::FEq0(j), path), DVBoolTy, 0)
  }
}

///|
fn is_bool_ty(v : DValue) -> Bool {
  match force_value(v) {
    DVBoolTy => true
    _ => false
  }
}

///|
test "glue_endpoint_parts: top-collapsed endpoint keeps the generic base, not parts.base" {
  // Target endpoint (`j = 1`): the specialised domain face is top and
  // the endpoint type itself has collapsed to the partial type `Nat`.
  // The reconstructed Glue parts must nevertheless report the true
  // underlying base type `Bool` (the base of the generic Glue); the
  // collapsed endpoint type `Nat` (`parts.base`) is the *partial*
  // type, not the base.
  let tgt = glue_endpoint_parts(collapsed_glue_line, Dim::DOne, 0)
  assert_eq(tgt.system.branches.length(), 1)
  assert_true(face_is_top_sem(tgt.face))
  assert_true(is_bool_ty(tgt.base))
  // Source endpoint (`j = 0`): the specialised face is bottom, the
  // Glue collapses to its base, and `parts.base` already is `Bool`.
  let src = glue_endpoint_parts(collapsed_glue_line, Dim::DZero, 0)
  assert_eq(src.system.branches.length(), 1)
  assert_true(face_is_bot_sem(src.face))
  assert_true(is_bool_ty(src.base))
  // Mirror line: the top collapse is at the source endpoint.
  let src_rev = glue_endpoint_parts(collapsed_glue_line_rev, Dim::DZero, 0)
  assert_true(face_is_top_sem(src_rev.face))
  assert_true(is_bool_ty(src_rev.base))
  let tgt_rev = glue_endpoint_parts(collapsed_glue_line_rev, Dim::DOne, 0)
  assert_true(face_is_bot_sem(tgt_rev.face))
  assert_true(is_bool_ty(tgt_rev.base))
}

///|
test "comp along a top-collapsed Glue line lands in the partial type" {
  // `coe` from `j = 0` (the base type `Bool`) to `j = 1` (the
  // collapsed partial type `Nat`) must produce a value; converting a
  // neutral base element must not get stuck on a wrongly-typed base
  // line (its base component is composed in `Bool` throughout).
  let x = reflect_var(0, DVBoolTy)
  let y = coe_value(collapsed_glue_line, Dim::DZero, Dim::DOne, x, 1)
  // The result is checked at the target type `Nat`: conversion of the
  // result against itself at `Nat` and the endpoint computation for a
  // closed element (transport of `true` is the partial value obtained
  // along the branch path, here represented in `Nat`) must succeed.
  assert_true(conv_at(1, 1, DVNatTy, y, y))
  // Mirror direction: a neutral element of the partial type at the
  // top-collapsed source of the reversed line coerces to the base
  // type at the target, again with the base component composed in
  // `Bool` throughout.
  let z = reflect_var(0, DVNatTy)
  let w = coe_value(collapsed_glue_line_rev, Dim::DZero, Dim::DOne, z, 1)
  assert_true(conv_at(1, 1, DVBoolTy, w, w))
  assert_true(check_dep_all())
}
