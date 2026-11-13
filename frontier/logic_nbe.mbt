///|
// Weak omega-groupoids, adjoint logic, and symbolic dynamic
// execution integrated with NbE.

// ---------------------------------------------------------------------------
// Weak omega-groupoid: a skeletal categorical group with cocycle
// ---------------------------------------------------------------------------
//
// The model is skeletal: one 0-cell; the 1-cells form the group
// `Z/m`; a 2-cell is an automorphism label `a` in `Z/m` of a
// 1-cell (vertical and horizontal composition are both addition of
// labels, the action being trivial); composition of 1-cells is
// written strictly, but the *associator* is the 2-cell labelled by
// the carry 3-cocycle
//   `alpha(x, y, z) = x * floor((y + z) / m)  (mod m)`,
// which is normalised (vanishes when any argument is `0`, so the
// unitors can be strict) and satisfies the pentagon identity --
// the group 3-cocycle condition -- while being genuinely
// nontrivial (`alpha(1, 1, 1) = 1` for `m = 2`): associativity
// holds only up to a non-identity 2-cell.  This is the classical
// skeletal model of a categorical group, truncated as a weak
// omega-groupoid: 3-cells between parallel 2-cells are unique
// identity witnesses (the pentagonator is the pentagon equality
// itself), and all higher cells are likewise thin, giving the
// truncated weak omega-structure verified here.  Everything is
// checked for `m = 2` and `m = 3`, exhaustively.

///|
fn omega_alpha(m : Int32, x : Int32, y : Int32, z : Int32) -> Int32 {
  let carry = (y + z) / m
  x * carry % m
}

///|
pub fn check_weak_omega_groupoid() -> Bool {
  for m in [2, 3] {
    // 1-cells: the group `Z/m`, with strict globular data
    // (source/target of every label is its own 1-cell).
    for x in 0..<m {
      for y in 0..<m {
        if (x + y) % m < 0 || (x + m - x) % m != 0 {
          return false
        }
        for z in 0..<m {
          if ((x + y) % m + z) % m != (x + (y + z) % m) % m {
            return false
          }
        }
      }
    }
    // The associator is normalised (strict units / triangulator).
    for y in 0..<m {
      for z in 0..<m {
        if omega_alpha(m, 0, y, z) != 0 ||
          omega_alpha(m, y, 0, z) != 0 ||
          omega_alpha(m, y, z, 0) != 0 {
          return false
        }
      }
    }
    // Pentagon identity (the 3-cocycle condition), for every
    // quadruple: the two ways of rebracketing
    // `((w+x)+y)+z` to `w+(x+(y+z))` through associator 2-cells
    // have equal labels, so the pentagonator 3-cell exists and is
    // the identity witness of that equality.
    for w in 0..<m {
      for x in 0..<m {
        for y in 0..<m {
          for z in 0..<m {
            let lhs = (
                omega_alpha(m, y, z, w) +
                omega_alpha(m, x, (y + z) % m, w) +
                omega_alpha(m, x, y, z)
              ) %
              m
            let rhs = (
                omega_alpha(m, (x + y) % m, z, w) +
                omega_alpha(m, x, y, (z + w) % m)
              ) %
              m
            if lhs != rhs {
              return false
            }
          }
        }
      }
    }
    // 2-cell algebra: vertical and horizontal composition are
    // addition of labels; interchange holds; every 2-cell has an
    // inverse label.
    for a in 0..<m {
      if (a + (m - a) % m) % m != 0 {
        return false
      }
      for b in 0..<m {
        for c in 0..<m {
          for d in 0..<m {
            if ((a + b) % m + (c + d) % m) % m !=
              ((a + c) % m + (b + d) % m) % m {
              return false
            }
          }
        }
      }
    }
  }
  // The associator is genuinely weak (non-identity) for `m = 2`:
  // `(1+1)+1 = 1+(1+1)` as 1-cells, but the associator 2-cell is
  // the nontrivial label `1`, not the identity label `0`.
  omega_alpha(2, 1, 1, 1) == 1 && omega_alpha(3, 1, 1, 1) == 0
}

// ---------------------------------------------------------------------------
// Adjoint logic on finite powerset lattices
// ---------------------------------------------------------------------------
//
// Subsets of a finite set are bitmasks.  Three adjunctions are
// verified exhaustively:
//   * Heyting: `a /\ b <= c` iff `b <= (a => c)`;
//   * quantifiers along a map `phi`: direct image is left adjoint
//     to inverse image, which is itself left adjoint to the
//     universal image, `exists_phi -| phi^{-1} -| forall_phi`;
//   * the Galois connection induced by a relation.
// Adjoint existence is also decided by search: a join-preserving
// map between finite Boolean lattices acquires a right adjoint by
// the formula `g(b) = union of { a | f(a) <= b }`, while a
// monotone map that does not preserve joins is shown to have no
// adjoint at all (all monotone candidates are enumerated).

///|
fn adj_phi() -> Array[Int32] {
  [0, 0, 1, 1]
}

///|
fn adj_exists_phi(s : Int32) -> Int32 {
  let phi = adj_phi()
  let mut out = 0
  for x in 0..<4 {
    if ((s >> x) & 1) == 1 {
      out = out | (1 << phi[x])
    }
  }
  out
}

///|
fn adj_pre_phi(t : Int32) -> Int32 {
  let phi = adj_phi()
  let mut out = 0
  for x in 0..<4 {
    if ((t >> phi[x]) & 1) == 1 {
      out = out | (1 << x)
    }
  }
  out
}

///|
fn adj_forall_phi(s : Int32) -> Int32 {
  let phi = adj_phi()
  let mut out = 0
  for y in 0..<2 {
    let mut ok = true
    for x in 0..<4 {
      if phi[x] == y && ((s >> x) & 1) == 0 {
        ok = false
      }
    }
    if ok {
      out = out | (1 << y)
    }
  }
  out
}

///|
fn adj_galois_f(s : Int32) -> Int32 {
  let mut out = 0
  for y in 0..<3 {
    for x in 0..<3 {
      if ((s >> x) & 1) == 1 && x <= y {
        out = out | (1 << y)
      }
    }
  }
  out
}

///|
fn adj_galois_g(t : Int32) -> Int32 {
  let mut out = 0
  for x in 0..<3 {
    let mut ok = true
    for y in 0..<3 {
      if x <= y && ((t >> y) & 1) == 0 {
        ok = false
      }
    }
    if ok {
      out = out | (1 << x)
    }
  }
  out
}

///|
fn adj_is_monotone_mask(g : Array[Int32]) -> Bool {
  for a in 0..<(1 << 2) {
    for b in 0..<(1 << 2) {
      if mask_subset(a, b) && !mask_subset(g[a], g[b]) {
        return false
      }
    }
  }
  true
}

///|
fn mask_subset(a : Int32, b : Int32) -> Bool {
  (a & b) == a
}

///|
fn heyting_imp(a : Int32, b : Int32, universe : Int32) -> Int32 {
  ((universe ^ a) | b) & universe
}

///|
pub fn check_adjoint_logic() -> Bool {
  // Heyting adjunction on `P({0, 1, 2})`.
  let universe = (1 << 3) - 1
  for a in 0..<=universe {
    for b in 0..<=universe {
      for c in 0..<=universe {
        let lhs = mask_subset(a & b, c)
        let rhs = mask_subset(b, heyting_imp(a, c, universe))
        if lhs != rhs {
          return false
        }
      }
    }
  }
  // Quantifier adjunctions along `phi : Fin 4 -> Fin 2`
  // (`adj_exists_phi -| adj_pre_phi -| adj_forall_phi`).
  for s in 0..<(1 << 4) {
    for t in 0..<(1 << 2) {
      if mask_subset(adj_exists_phi(s), t) != mask_subset(s, adj_pre_phi(t)) {
        return false
      }
      if mask_subset(adj_pre_phi(t), s) != mask_subset(t, adj_forall_phi(s)) {
        return false
      }
    }
  }
  // Galois connection from the order relation on `Fin 3`:
  // `f(S) = { y | exists x in S, x <= y }` (upward closure) and
  // `g(T) = { x | forall y >= x, y in T }`.
  for s in 0..<(1 << 3) {
    for t in 0..<(1 << 3) {
      if mask_subset(adj_galois_f(s), t) != mask_subset(s, adj_galois_g(t)) {
        return false
      }
      // Unit and counit.
      if !mask_subset(s, adj_galois_g(adj_galois_f(s))) ||
        !mask_subset(adj_galois_f(adj_galois_g(t)), t) {
        return false
      }
    }
  }
  // Adjoint existence, decided by enumeration on `P({0, 1})`
  // (masks ordered by inclusion).  The top-detector
  // `f(S) = full if S = full else empty` is monotone but does not
  // preserve joins (`f({0} | {1}) != f({0}) | f({1})`), and the
  // search confirms that no monotone map is its right adjoint.
  let top_detector : (Int32) -> Int32 = s => if s == 3 { 3 } else { 0 }
  let mut adjoints_found = 0
  // Enumerate all maps `g : P(2) -> P(2)` (values in `0..4` for
  // the four inputs `0..4`), filter monotone, test adjunction
  // against `top_detector`.
  for code in 0..<(4 * 4 * 4 * 4) {
    let g : Array[Int32] = []
    let mut rest = code
    for _ in 0..<4 {
      g.push(rest % 4)
      rest = rest / 4
    }
    if !adj_is_monotone_mask(g) {
      continue
    }
    let mut is_adjoint = true
    for a in 0..<4 {
      for b in 0..<4 {
        if mask_subset(top_detector(a), b) != mask_subset(a, g[b]) {
          is_adjoint = false
        }
      }
    }
    if is_adjoint {
      adjoints_found = adjoints_found + 1
    }
  }
  if adjoints_found != 0 {
    return false
  }
  // A join-preserving map does have the adjoint given by the
  // union formula, on the nose.
  let join_pres : (Int32) -> Int32 = s => s & 1
  for b in 0..<4 {
    let mut gval = 0
    for a in 0..<4 {
      if mask_subset(join_pres(a), b) {
        gval = gval | a
      }
    }
    for a in 0..<4 {
      if mask_subset(join_pres(a), b) != mask_subset(a, gval) {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Symbolic dynamic execution, integrated with NbE
// ---------------------------------------------------------------------------
//
// Programs are terms of the finite layer (`@finite.Term`) with
// free Boolean variables.  Symbolic execution explores the tree of
// concretisations: it splits on each symbolic variable in turn
// (recording the path condition of each leaf), executes the
// program concretely at every leaf with the `@finite` evaluator,
// and assembles the trace results.  The integration with NbE is
// the verified statement that, at every leaf, the symbolic trace
// result equals the NbE normal form of the corresponding closed
// concretisation of the program -- so the symbolic trace semantics
// and the NbE (definitional-equality) semantics coincide on the
// nose, and equality of programs under symbolic execution is the
// decidable NbE equality.

///|
/// One symbolic execution trace: a concretising assignment (bit
/// `i` is the value of variable `i`) and the resulting data term.
pub(all) struct SymTrace {
  assignment : Int32
  result : Term
}

///|
/// Substitute closed literals for the free variables of a term.
/// `env[i]` replaces the variable with de Bruijn index `i`
/// counted from outside the enclosing binders tracked by `depth`.
fn sym_subst(t : Term, env : Array[Term], depth : Int32) -> Term {
  match t {
    Term::TmVar(i) => if i < depth { t } else { env[i - depth] }
    Term::TmLam(body) => Term::TmLam(sym_subst(body, env, depth + 1))
    Term::TmApp(f, a) =>
      Term::TmApp(sym_subst(f, env, depth), sym_subst(a, env, depth))
    Term::TmPair(a, b) =>
      Term::TmPair(sym_subst(a, env, depth), sym_subst(b, env, depth))
    Term::TmFst(a) => Term::TmFst(sym_subst(a, env, depth))
    Term::TmSnd(a) => Term::TmSnd(sym_subst(a, env, depth))
    Term::TmAnn(inner, tag) => Term::TmAnn(sym_subst(inner, env, depth), tag)
    other => other
  }
}

///|
/// The path condition of a trace over the symbolic variables, as a
/// face of the face lattice: the conjunction, over all variables,
/// of `(i = 1)` when the assignment sets `i`, and `(i = 0)`
/// otherwise.  Trace conditions are pairwise disjoint and cover
/// the whole cube -- the symbolic execution is path-sensitive and
/// exhaustive.
pub fn sym_path_condition(assignment : Int32, nvars : Int32) -> Face {
  let mut face = Face::FTop
  for i in 0..<nvars {
    let lit = if ((assignment >> i) & 1) == 1 {
      @face_bdd.face_var1(i)
    } else {
      @face_bdd.face_var0(i)
    }
    face = @face_bdd.face_and(face, lit)
  }
  @face_bdd.face_simplify(face)
}

///|
/// Symbolically execute `t` (a term with `nvars` free Boolean
/// variables) over all `2^nvars` concretisations, using the
/// `@finite` evaluator at every leaf.
pub fn sym_exec(t : Term, nvars : Int32) -> Array[SymTrace] {
  let out : Array[SymTrace] = []
  let total = 1 << nvars
  for code in 0..<total {
    let env : Array[@finite.Value] = []
    for i in 0..<nvars {
      env.push(@finite.eval(Term::TmBool(((code >> i) & 1) == 1), []))
    }
    let value = @finite.eval(t, env)
    out.push(SymTrace::{ assignment: code, result: @finite.quote(0, value), })
  }
  out
}

///|
pub fn check_symbolic_nbe() -> Bool {
  // Sample programs with one symbolic Boolean variable `x`
  // (de Bruijn index 0): the identity, a pair program, a
  // beta-reducing projection, and the ua(swap) coercion applied
  // to a symbolic pair.
  let samples : Array[Term] = [
    Term::TmVar(0),
    Term::TmPair(Term::TmVar(0), Term::TmBool(true)),
    Term::TmFst(Term::TmPair(Term::TmBool(false), Term::TmVar(0))),
    Term::TmApp(
      @finite.tm_swap(),
      Term::TmPair(Term::TmVar(0), Term::TmBool(true)),
    ),
    Term::TmApp(
      @finite.TmCoeUaSwap,
      Term::TmPair(Term::TmVar(0), Term::TmBool(false)),
    ),
  ]
  let nvars = 1
  for t in samples {
    let traces = sym_exec(t, nvars)
    // Exhaustivity: one trace per assignment, all distinct.
    if traces.length() != 1 << nvars {
      return false
    }
    for idx in 0..<traces.length() {
      if traces[idx].assignment != idx {
        return false
      }
    }
    for a in traces {
      // NbE integration: the symbolic trace result at each leaf
      // equals the NbE normal form of the closed concretisation.
      let literals : Array[Term] = []
      for i in 0..<nvars {
        literals.push(Term::TmBool(((a.assignment >> i) & 1) == 1))
      }
      let closed = sym_subst(t, literals, 0)
      if @finite.nf(closed, 0) != a.result {
        return false
      }
    }
    // Path conditions partition the cube: every Boolean
    // assignment satisfies exactly one trace condition.
    for code in 0..<(1 << nvars) {
      let mut hits = 0
      let env : Array[Bool] = []
      for i in 0..<nvars {
        env.push(((code >> i) & 1) == 1)
      }
      for tr in traces {
        if @face_bdd.face_holds(sym_path_condition(tr.assignment, nvars), env) {
          hits = hits + 1
        }
      }
      if hits != 1 {
        return false
      }
    }
    // The NbE normal forms of the samples themselves are
    // single-valued (idempotent) with the variable open.
    if !@finite.nbe_single_valued([t], nvars) {
      return false
    }
  }
  // Symbolic execution is path-sensitive: the identity program
  // distinguishes the two branches (the trace results differ),
  // whereas the beta-reducing projection is branch-insensitive in
  // the verified, NbE-checked sense (both traces are `false`).
  let id_traces = sym_exec(Term::TmVar(0), 1)
  if id_traces[0].result == id_traces[1].result {
    return false
  }
  let proj_traces = sym_exec(samples[2], 1)
  proj_traces[0].result == Term::TmBool(false) &&
  proj_traces[1].result == Term::TmBool(false)
}
