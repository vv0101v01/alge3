///|
fn some_or(x : Int32?, fallback : Int32) -> Int32 {
  match x {
    Some(v) => v
    None => fallback
  }
}

///|
fn iso_exn(o : Iso?) -> Iso {
  match o {
    Some(e) => e
    None => Iso::id(0)
  }
}

///|
/// The Glue line over one dimension that glues `Bool` to itself along
/// negation on the face `(i = 0)`.
fn glue_not_line() -> (Cof, CubeTy, CubeTy, Array[Array[Int32]], CubeTy) {
  let phi = face_cof(0, 0)
  let t = const_ty(1, 2)
  let a = const_ty(1, 2)
  let e : Array[Array[Int32]] = [[1, 0], [], []]
  (phi, t, a, e, glue_ty(phi, t, a, e))
}

///|
test "CubeTy: presheaf laws for all type formers" {
  assert_true(const_ty(2, 3).check())
  assert_true(prod_ty(const_ty(2, 2), const_ty(2, 3)).check())
  let (phi, t, a, e, g) = glue_not_line()
  assert_true(check_glue_data(phi, t, a, e))
  assert_true(g.check())
  assert_true(face_ty(g, 0, 0).check())
  assert_true(reverse_ty(g, 0).check())
  assert_true(extend_ty(g).check())
  let not_iso = iso_exn(perm_iso([1, 0]))
  let fibs = [ua(not_iso), const_ty(1, 3)]
  assert_true(sigma_const_ty(fibs).check())
  assert_true(pi_const_ty(fibs).check())
  assert_true(path_ty(const_ty(1, 2), 0, 0).check())
  assert_true(fun_ty(ua(not_iso), ua(not_iso)).check())
  assert_true(all_res_bijective(ua(not_iso)))
}

///|
test "Glue: strict face, glue and unglue compute" {
  let (phi, t, a, e, g) = glue_not_line()
  // restriction generic -> 0 is e^{-1} = not; generic -> 1 is the identity
  assert_eq(g.restrict(2, 0, 0), 1)
  assert_eq(g.restrict(2, 0, 1), 0)
  assert_eq(g.restrict(2, 1, 0), 0)
  assert_eq(g.restrict(2, 1, 1), 1)
  // unglue at the glued face applies e; at the generic stage it is the base value
  assert_eq(unglue_at(phi, t, a, e, 0, 0), 1)
  assert_eq(unglue_at(phi, t, a, e, 0, 1), 0)
  assert_eq(unglue_at(phi, t, a, e, 2, 1), 1)
  // glue: partial value t=1 on (i=0) is compatible with base value b=0 only
  let u = PartialElem::new(phi, [0], [1])
  assert_true(check_partial(t, u))
  assert_eq(some_or(glue_at(phi, t, a, e, 2, u, 0), -1), 0)
  assert_eq(some_or(glue_at(phi, t, a, e, 2, u, 1), -1), -1)
  // on the face itself, glue returns the partial value strictly
  assert_eq(some_or(glue_at(phi, t, a, e, 0, u, 0), -1), 1)
}

///|
test "transport in a Glue type is the glued equivalence" {
  let (_, _, _, _, g) = glue_not_line()
  // transp^i Glue = e: the computational heart of ua-beta
  assert_eq(some_or(transp_line(g, 0, 0), -1), 1)
  assert_eq(some_or(transp_line(g, 0, 1), -1), 0)
  // and backwards along the reversed line is e^{-1} = not
  let rg = reverse_ty(g, 0)
  assert_eq(some_or(transp_line(rg, 0, 0), -1), 1)
  assert_eq(some_or(transp_line(rg, 0, 1), -1), 0)
}

///|
test "comp and hcomp: fillers, unique lids, ill-formed boxes" {
  let x = const_ty(1, 2)
  let ext = extend_ty(x)
  // tube on the face (y = 0) of the square, value 1 (component stage [0, *] = 6)
  let tube = PartialElem::new(face_cof(0, 0), [6], [1])
  assert_true(check_partial(ext, tube))
  match hcomp(x, tube, 1) {
    Some(r) => {
      assert_eq(r.lid, 1)
      assert_eq(r.fillers, 1)
      assert_true(r.unique_lid)
      // the filler restricts to the cap and the lid
      assert_eq(ext.restrict(8, 2, r.filler), 1)
      assert_eq(ext.restrict(8, 5, r.filler), 1)
    }
    None => assert_true(false)
  }
  // a cap disagreeing with the tube has no filler
  match hcomp(x, tube, 0) {
    Some(_) => assert_true(false)
    None => assert_true(true)
  }
  // an incompatible system is rejected before filling
  let bad = PartialElem::new(face_cof(0, 0), [6, 0], [1, 0])
  assert_false(check_partial(ext, bad))
  // transport along refl is the identity, with a constant filler
  let rl = refl_line(3)
  assert_eq(some_or(transp_line(rl, 0, 2), -1), 2)
  let f = some_or(fill_line(rl, 0, 2), -1)
  assert_eq(rl.restrict(2, 0, f), 2)
  assert_eq(rl.restrict(2, 1, f), 2)
}

///|
test "comp in a Glue square: the tube passes through the glued face" {
  // dims: x = 0 (composition), y = 1 (glued face y = 0, equivalence not)
  let phi = face_cof(1, 0)
  let t = const_ty(2, 2)
  let a = const_ty(2, 2)
  let e : Array[Array[Int32]] = []
  for code in 0..<9 {
    if subcube_digit(code, 1) == 0 {
      e.push([1, 0])
    } else {
      e.push([])
    }
  }
  assert_true(check_glue_data(phi, t, a, e))
  let g = glue_ty(phi, t, a, e)
  assert_true(g.check())
  // tube on (y = 0): component stage [*, 0] = 2, value 1 in T.
  // cap 0 at x = 0 is compatible, since the generic cube 0 restricts to
  // e^{-1}(0) = 1 on the glued face.
  let tube = PartialElem::new(face_cof(1, 0), [2], [1])
  assert_true(check_partial(g, tube))
  match comp(g, 0, tube, 0) {
    Some(r) => {
      assert_eq(r.lid, 0)
      assert_eq(r.filler, 0)
      assert_true(r.unique_lid)
    }
    None => assert_true(false)
  }
  // the wrong tube value admits no filler
  let tube_bad = PartialElem::new(face_cof(1, 0), [2], [0])
  match comp(g, 0, tube_bad, 0) {
    Some(_) => assert_true(false)
    None => assert_true(true)
  }
  // transport along y out of the glued face applies e = not
  assert_eq(some_or(transp_line(g, 1, 0), -1), 1)
  assert_eq(some_or(transp_line(g, 1, 1), -1), 0)
}

///|
test "comp in Sigma and Pi over a constant base is componentwise" {
  let not_iso = iso_exn(perm_iso([1, 0]))
  let rot3 = iso_exn(perm_iso([1, 2, 0]))
  let sig = sigma_const_ty([ua(not_iso), ua(rot3)])
  // face 0: codes (0,v)=v in 0..2, (1,v)=2+v; transport applies not / rot3
  let expected_sig = [1, 0, 3, 4, 2]
  for c in 0..<5 {
    assert_eq(some_or(transp_line(sig, 0, c), -1), expected_sig[c])
  }
  let pi = pi_const_ty([ua(not_iso), ua(not_iso)])
  // tuples (v0, v1) coded v0 + 2 v1; transport negates both components
  let expected_pi = [3, 2, 1, 0]
  for c in 0..<4 {
    assert_eq(some_or(transp_line(pi, 0, c), -1), expected_pi[c])
  }
  // the same maps read off as stage-line isomorphisms
  match stage_line_iso(sig, 2, 0) {
    Some(iso) => assert_true(fn_eq(iso.fwd, expected_sig))
    None => assert_true(false)
  }
}

///|
test "path types: paths in discrete types are equality; paths in lines" {
  let b = const_ty(1, 2)
  assert_eq(path_ty(b, 0, 0).generic_card(), 1)
  assert_eq(path_ty(b, 0, 1).generic_card(), 0)
  assert_eq(path_ty(b, 1, 1).generic_card(), 1)
  assert_eq(path_ty(const_ty(0, 2), 1, 1).card[0], 1)
  // paths between sections of the ua(not) line: only refl-like squares
  let not_iso = iso_exn(perm_iso([1, 0]))
  let line = ua(not_iso)
  assert_eq(path_ty(line, 0, 0).generic_card(), 1)
  assert_eq(path_ty(line, 0, 1).generic_card(), 0)
  assert_true(path_ty(line, 0, 0).check())
}
