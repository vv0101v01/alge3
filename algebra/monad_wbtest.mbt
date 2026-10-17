///|
fn sample_term() -> Term {
  // (x + 2) * (y + 3)
  Node(1, [Node(0, [Var(0), Lit(2)]), Node(0, [Var(1), Lit(3)])])
}

///|
fn arith_alg() -> Algebra {
  Algebra::{
    carrier_size: 1000000,
    ops: [fn(xs) { xs[0] + xs[1] }, fn(xs) { xs[0] * xs[1] }],
  }
}

///|
test "monad laws for substitution" {
  let t = sample_term()
  let f : Array[Term] = [Lit(10), Var(2)]
  let g : Array[Term] = [Var(0), Lit(7), Lit(1)]
  // left unit: subst (pure x) f = f x
  assert_eq(pure(0).subst(f), f[0])
  // right unit: subst t (Var i) = t
  let id_env : Array[Term] = [Var(0), Var(1), Var(2)]
  assert_eq(t.subst(id_env), t)
  // associativity: subst (subst t f) g = subst t (subst f g)
  let left = t.subst(f).subst(g)
  let fg : Array[Term] = []
  for x in f {
    fg.push(x.subst(g))
  }
  assert_eq(left, t.subst(fg))
}

///|
test "fold is invariant under constant folding" {
  let alg = arith_alg()
  let t = Node(0, [Node(1, [Lit(3), Lit(4)]), Node(1, [Lit(5), Lit(6)])])
  assert_eq(fold(alg, t), 42)
  let o = optimize(alg, t)
  assert_eq(fold(alg, o), fold(alg, t))
  assert_eq(o, Lit(42))
}

///|
test "distributive law hexagon" {
  // pure_list x = [x]; pure_option x = Some x
  let x = 7
  let left = dist_list_option([Some(x)])
  let right = match left {
    Some(xs) => Some(xs[0])
    None => None
  }
  assert_eq(right, Some(x))
  assert_eq(dist_list_option([Some(1), None, Some(3)]), None)
  assert_eq(dist_list_option([Some(1), Some(3)]), Some([1, 3]))
}

///|
test "substitution cost is linear in tree size for a fixed environment" {
  let t = sample_term()
  let env : Array[Term] = [Lit(1), Lit(2)]
  assert_eq(subst_cost(t, env), 7)
  assert_eq(t.size(), 7)
}
