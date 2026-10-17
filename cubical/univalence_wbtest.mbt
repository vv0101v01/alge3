///|
fn some_or2(x : Int32?, fallback : Int32) -> Int32 {
  match x {
    Some(v) => v
    None => fallback
  }
}

///|
fn iso_exn2(o : Iso?) -> Iso {
  match o {
    Some(e) => e
    None => Iso::id(0)
  }
}

///|
test "ua: strict endpoints, and transport along ua(e) computes to e (ua-beta)" {
  let not_iso = iso_exn2(perm_iso([1, 0]))
  let p = ua(not_iso)
  assert_true(p.check())
  // endpoints are strict: the faces of the Glue line are A and B themselves
  assert_eq(p.card[0], 2)
  assert_eq(p.card[1], 2)
  assert_eq(face_ty(p, 0, 0).card[0], 2)
  assert_eq(face_ty(p, 0, 1).card[0], 2)
  // ua-beta as a computation: comp in the Glue line applies negation
  assert_eq(some_or2(transport_path(p, 0), -1), 1)
  assert_eq(some_or2(transport_path(p, 1), -1), 0)
  // exhaustively: every equivalence of Fin 3 and Fin 4 satisfies ua-beta
  assert_eq(all_permutations(3).length(), 6)
  assert_eq(all_permutations(4).length(), 24)
  let mut checked = 0
  for f in all_permutations(3) {
    assert_true(check_ua_beta(iso_exn2(perm_iso(f))))
    checked = checked + 1
  }
  for f in all_permutations(4) {
    assert_true(check_ua_beta(iso_exn2(perm_iso(f))))
    checked = checked + 1
  }
  assert_eq(checked, 30)
  // ua(id) transports trivially
  let pid = ua(Iso::id(3))
  for a in 0..<3 {
    assert_eq(some_or2(transport_path(pid, a), -1), a)
  }
}

///|
test "idtoeqv and ua are inverse: both round trips of univalence" {
  // idtoeqv (ua e) = e, for all equivalences of Fin 4
  for f in all_permutations(4) {
    let e = iso_exn2(perm_iso(f))
    match idtoeqv(ua(e)) {
      Some(g) => assert_true(fn_eq(g.fwd, e.fwd) && fn_eq(g.bwd, e.bwd))
      None => assert_true(false)
    }
  }
  // ua (idtoeqv p) is naturally stage-isomorphic to p, for a hand-built
  // line whose generic restrictions are both nontrivial
  let line = build_ty(1, [3, 3, 3], fn(big, face) {
    if big == 2 && face == 0 {
      [1, 2, 0]
    } else if big == 2 && face == 1 {
      [2, 0, 1]
    } else {
      fn_id(3)
    }
  })
  assert_true(line.check())
  assert_true(check_ua_eta(line))
  // its transport is res_1 o res_0^{-1} = [1, 2, 0]
  match idtoeqv(line) {
    Some(e) => assert_true(fn_eq(e.fwd, [1, 2, 0]))
    None => assert_true(false)
  }
  // the eta round trip also holds for refl, ua lines and reversed lines
  assert_true(check_ua_eta(refl_line(4)))
  for f in all_permutations(3) {
    let p = ua(iso_exn2(perm_iso(f)))
    assert_true(check_ua_eta(p))
    assert_true(check_ua_eta(sym_line(p)))
  }
}

///|
test "comp in U: path composition and symmetry in the finite universe" {
  let e = iso_exn2(perm_iso([1, 2, 0])) // rotate
  let g = iso_exn2(perm_iso([1, 0, 2])) // swap 0 1
  // symmetry: transport along sym (ua e) is e^{-1}
  match idtoeqv(sym_line(ua(e))) {
    Some(h) => assert_true(fn_eq(h.fwd, e.bwd))
    None => assert_true(false)
  }
  // transitivity via comp in U: transport is g o e = [0, 2, 1]
  match comp_path_universe(ua(e), ua(g)) {
    Some(r) => {
      assert_true(r.check())
      assert_eq(r.card[0], 3)
      assert_eq(r.card[1], 3)
      match idtoeqv(r) {
        Some(h) => assert_true(fn_eq(h.fwd, [0, 2, 1]))
        None => assert_true(false)
      }
      for a in 0..<3 {
        assert_eq(some_or2(transport_path(r, a), -1), g.fwd[e.fwd[a]])
      }
      // the composite line is itself a ua line up to natural isomorphism
      assert_true(check_ua_eta(r))
    }
    None => assert_true(false)
  }
  // unit laws at the level of transport
  match comp_path_universe(refl_line(3), ua(g)) {
    Some(r) =>
      match idtoeqv(r) {
        Some(h) => assert_true(fn_eq(h.fwd, g.fwd))
        None => assert_true(false)
      }
    None => assert_true(false)
  }
  match comp_path_universe(ua(e), refl_line(3)) {
    Some(r) =>
      match idtoeqv(r) {
        Some(h) => assert_true(fn_eq(h.fwd, e.fwd))
        None => assert_true(false)
      }
    None => assert_true(false)
  }
  // ua(not) . ua(not) on Bool has identity transport
  let not_iso = iso_exn2(perm_iso([1, 0]))
  match comp_path_universe(ua(not_iso), ua(not_iso)) {
    Some(r) =>
      match idtoeqv(r) {
        Some(h) => assert_true(fn_eq(h.fwd, [0, 1]))
        None => assert_true(false)
      }
    None => assert_true(false)
  }
  // associativity of path composition at the level of transport
  let h3 = iso_exn2(perm_iso([2, 1, 0]))
  let lhs = match comp_path_universe(ua(e), ua(g)) {
    Some(r) => comp_path_universe(r, ua(h3))
    None => None
  }
  let rhs = match comp_path_universe(ua(g), ua(h3)) {
    Some(r) => comp_path_universe(ua(e), r)
    None => None
  }
  match (lhs, rhs) {
    (Some(l), Some(r)) =>
      match (idtoeqv(l), idtoeqv(r)) {
        (Some(le), Some(re)) => assert_true(fn_eq(le.fwd, re.fwd))
        _ => assert_true(false)
      }
    _ => assert_true(false)
  }
}

///|
test "transport of structure along ua(not): AND becomes OR" {
  let not_iso = iso_exn2(perm_iso([1, 0]))
  let line = ua(not_iso)
  let dom = prod_ty(line, line)
  let funs = fun_ty(dom, line)
  assert_true(funs.check())
  // binary operations coded by their tables over inputs (x*2 + y):
  // AND = [0,0,0,1] -> code 8; OR = [0,1,1,1] -> code 14
  assert_eq(some_or2(transp_line(funs, 0, 8), -1), 14)
  // and back: OR becomes AND (De Morgan, by computation)
  assert_eq(some_or2(transp_line(funs, 0, 14), -1), 8)
  // XOR = [0,1,1,0] -> code 6: conjugating by negation on both inputs
  // indeed not(x xor y) with both inputs negated: (~x) xor (~y) = x xor y,
  // then negated output gives XNOR = [1,0,0,1] -> code 9
  assert_eq(some_or2(transp_line(funs, 0, 6), -1), 9)
  // the transported operation is still associative and commutative:
  // decode OR (code 14) and check the semigroup laws on all triples
  let table = [0, 1, 1, 1]
  for x in 0..<2 {
    for y in 0..<2 {
      assert_eq(table[x * 2 + y], table[y * 2 + x])
      for z in 0..<2 {
        assert_eq(
          table[table[x * 2 + y] * 2 + z],
          table[x * 2 + table[y * 2 + z]],
        )
      }
    }
  }
  // unary operations: negation [1,0] (code 1) is fixed; const-false
  // [0,0] (code 0) becomes const-true [1,1] (code 3)
  let unary = fun_ty(line, line)
  assert_eq(some_or2(transp_line(unary, 0, 1), -1), 1)
  assert_eq(some_or2(transp_line(unary, 0, 0), -1), 3)
  // identity [0,1] (code 2) is fixed
  assert_eq(some_or2(transp_line(unary, 0, 2), -1), 2)
}
