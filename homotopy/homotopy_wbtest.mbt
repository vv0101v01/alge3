///|
test "monoid bar construction" {
  let t = trivial_monoid()
  assert_true(t.is_associative())
  assert_eq(bar_betti(t, 4), [1, 0, 0, 0, 0])
  let z2 = cyclic_group(2)
  assert_eq(bar_betti(z2, 4), [1, 1, 1, 1, 1])
  let z3 = cyclic_group(3)
  assert_eq(bar_betti(z3, 4), [1, 0, 0, 0, 0])
  assert_true(bar_complex(z3, 4).check_d2())
}

///|
test "span composition is associative and unital" {
  let a_rows : Array[Bits] = []
  let r0 = Bits::new(3)
  r0.set(0)
  r0.set(2)
  a_rows.push(r0)
  let r1 = Bits::new(3)
  r1.set(1)
  a_rows.push(r1)
  let r2 = Bits::new(3)
  r2.set(0)
  r2.set(1)
  r2.set(2)
  a_rows.push(r2)
  let r = Span::new(3, 3, BoolMat::new(a_rows, 3))
  let s = Span::new(3, 3, BoolMat::identity(3))
  let rs = r.compose(s)
  let sr = s.compose(r)
  for i in 0..<3 {
    for j in 0..<3 {
      assert_eq(rs.rel.get(i, j), r.rel.get(i, j))
      assert_eq(sr.rel.get(i, j), r.rel.get(i, j))
    }
  }
  let rr = r.compose(r).compose(r)
  let rrr = r.compose(r.compose(r))
  for i in 0..<3 {
    for j in 0..<3 {
      assert_eq(rr.rel.get(i, j), rrr.rel.get(i, j))
    }
  }
}

///|
test "span composition equals explicit pullback" {
  // X -> A x B with 3 points; Y -> B x C with 3 points.
  let f : Array[Int32] = [0, 1, 2]
  let g : Array[Int32] = [0, 0, 1]
  let h : Array[Int32] = [0, 1, 1]
  let k : Array[Int32] = [0, 2, 2]
  let s = span_of_maps(3, 2, f, g)
  let t = span_of_maps(2, 3, h, k)
  let comp = s.compose(t)
  let pb = pullback_compose(3, 2, 3, f, g, h, k)
  for i in 0..<3 {
    for j in 0..<3 {
      assert_eq(comp.rel.get(i, j), pb.get(i, j))
    }
  }
}
