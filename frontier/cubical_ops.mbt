///|
// De Morgan cubical algebra, small cubical operators, and the
// decidability / confluence of dimension-term rewriting.
//
// The interval layer (`@cubical`) already decides equality of
// dimension terms by canonical DNF.  This file adds:
//   1. an exhaustive axiomatic verification of the De Morgan
//      algebra (a bounded distributive lattice with an involutive
//      De Morgan negation that is *not* Boolean) on all dimension
//      terms of bounded size, cross-checked against cofibration
//      entailment in the face lattice;
//   2. the small cubical operators -- face restriction, degeneracy,
//      reversal, and the two connections (merging adjacent
//      coordinates by Kleene `and` / `or`) -- on the finite cubes
//      `{0, 1, *}^n` for `n <= 3`, with their cubical identities
//      verified on every subcube / Kleene assignment;
//   3. an explicit rewrite system for dimension terms (push
//      negations to atoms, eliminate bounds and idempotents,
//      distribute `and` over `or`), a from-scratch DNF decision
//      procedure, and a finite confluence check: every one-step
//      reduct of every small term joins at the same normal form.

// ---------------------------------------------------------------------------
// De Morgan cubical algebra
// ---------------------------------------------------------------------------

///|
fn dm_atoms() -> Array[Dim] {
  [Dim::DZero, Dim::DOne, Dim::DVar(0), Dim::DVar(1)]
}

///|
/// All dimension terms built from atoms by one unary/binary step.
fn dm_terms1() -> Array[Dim] {
  let atoms = dm_atoms()
  let out : Array[Dim] = []
  for a in atoms {
    out.push(a)
    out.push(Dim::DNeg(a))
  }
  for a in atoms {
    for b in atoms {
      out.push(Dim::DAnd(a, b))
      out.push(Dim::DOr(a, b))
    }
  }
  out
}

///|
/// A slightly larger pool used for ternary laws.
fn dm_pool() -> Array[Dim] {
  let i = Dim::DVar(0)
  let j = Dim::DVar(1)
  [
    Dim::DZero,
    Dim::DOne,
    i,
    j,
    Dim::DNeg(i),
    Dim::DNeg(j),
    Dim::DAnd(i, j),
    Dim::DOr(i, j),
    Dim::DNeg(Dim::DAnd(i, j)),
    Dim::DNeg(Dim::DOr(i, j)),
    Dim::DAnd(i, Dim::DNeg(j)),
    Dim::DOr(Dim::DNeg(i), j),
  ]
}

///|
pub fn check_de_morgan_cubical_algebra() -> Bool {
  let terms = dm_terms1()
  let pool = dm_pool()
  let zero = Dim::DZero
  let one = Dim::DOne
  // Unary and binary laws on all one-step terms.
  for a in terms {
    if !@face_bdd.dim_eq_demorgan(Dim::DNeg(Dim::DNeg(a)), a) {
      return false
    }
    if !@face_bdd.dim_eq_demorgan(Dim::DAnd(a, a), a) ||
      !@face_bdd.dim_eq_demorgan(Dim::DOr(a, a), a) {
      return false
    }
    if !@face_bdd.dim_eq_demorgan(Dim::DAnd(a, one), a) ||
      !@face_bdd.dim_eq_demorgan(Dim::DOr(a, zero), a) {
      return false
    }
    if !@face_bdd.dim_eq_demorgan(Dim::DAnd(a, zero), zero) ||
      !@face_bdd.dim_eq_demorgan(Dim::DOr(a, one), one) {
      return false
    }
    for b in terms {
      if !@face_bdd.dim_eq_demorgan(Dim::DAnd(a, b), Dim::DAnd(b, a)) ||
        !@face_bdd.dim_eq_demorgan(Dim::DOr(a, b), Dim::DOr(b, a)) {
        return false
      }
      // De Morgan laws.
      if !@face_bdd.dim_eq_demorgan(
          Dim::DNeg(Dim::DAnd(a, b)),
          Dim::DOr(Dim::DNeg(a), Dim::DNeg(b)),
        ) ||
        !@face_bdd.dim_eq_demorgan(
          Dim::DNeg(Dim::DOr(a, b)),
          Dim::DAnd(Dim::DNeg(a), Dim::DNeg(b)),
        ) {
        return false
      }
      // Absorption.
      if !@face_bdd.dim_eq_demorgan(Dim::DOr(a, Dim::DAnd(a, b)), a) ||
        !@face_bdd.dim_eq_demorgan(Dim::DAnd(a, Dim::DOr(a, b)), a) {
        return false
      }
    }
  }
  // Ternary laws on the larger pool.
  for a in pool {
    for b in pool {
      for c in pool {
        if !@face_bdd.dim_eq_demorgan(
            Dim::DAnd(Dim::DAnd(a, b), c),
            Dim::DAnd(a, Dim::DAnd(b, c)),
          ) ||
          !@face_bdd.dim_eq_demorgan(
            Dim::DOr(Dim::DOr(a, b), c),
            Dim::DOr(a, Dim::DOr(b, c)),
          ) {
          return false
        }
        if !@face_bdd.dim_eq_demorgan(
            Dim::DAnd(a, Dim::DOr(b, c)),
            Dim::DOr(Dim::DAnd(a, b), Dim::DAnd(a, c)),
          ) ||
          !@face_bdd.dim_eq_demorgan(
            Dim::DOr(a, Dim::DAnd(b, c)),
            Dim::DAnd(Dim::DOr(a, b), Dim::DOr(a, c)),
          ) {
          return false
        }
      }
    }
  }
  // The interval is not Boolean: `i /\ ~i` is not `0` and
  // `i \/ ~i` is not `1` in the free De Morgan algebra.
  let i = Dim::DVar(0)
  if @face_bdd.dim_eq_demorgan(Dim::DAnd(i, Dim::DNeg(i)), zero) ||
    @face_bdd.dim_eq_demorgan(Dim::DOr(i, Dim::DNeg(i)), one) {
    return false
  }
  // Connection endpoint laws: `(i /\ j)[j := 0] = 0`,
  // `(i /\ j)[j := 1] = i`, and dually for `\/`.
  let j = Dim::DVar(1)
  if !@face_bdd.dim_eq_demorgan(
      @face_bdd.dim_subst(Dim::DAnd(i, j), 1, false),
      zero,
    ) ||
    !@face_bdd.dim_eq_demorgan(@face_bdd.dim_subst(Dim::DAnd(i, j), 1, true), i) ||
    !@face_bdd.dim_eq_demorgan(@face_bdd.dim_subst(Dim::DOr(i, j), 1, false), i) ||
    !@face_bdd.dim_eq_demorgan(
      @face_bdd.dim_subst(Dim::DOr(i, j), 1, true),
      one,
    ) {
    return false
  }
  // Face-lattice entailment agrees with the extensional (subcube)
  // semantics, and is a preorder.
  let cofs : Array[Cof] = [
    @cubical.face_cof(0, 0),
    @cubical.face_cof(0, 1),
    @cubical.face_cof(1, 0),
    @cubical.face_cof(0, 0).disj(@cubical.face_cof(1, 1)),
    @cubical.face_cof(0, 0).conj(@cubical.face_cof(1, 1)),
  ]
  for phi in cofs {
    if !@cubical.cof_entails(phi, phi, 2) {
      return false
    }
    for psi in cofs {
      let mut extensional = true
      for code in 0..<@cubical.pow3(2) {
        if phi.holds_code(code, 2) && !psi.holds_code(code, 2) {
          extensional = false
        }
      }
      if @cubical.cof_entails(phi, psi, 2) != extensional {
        return false
      }
      for chi in cofs {
        if @cubical.cof_entails(phi, psi, 2) &&
          @cubical.cof_entails(psi, chi, 2) &&
          !@cubical.cof_entails(phi, chi, 2) {
          return false
        }
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Small cubical operators on `{0, 1, *}^n`
// ---------------------------------------------------------------------------

///|
fn int_arr_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for k in 0..<a.length() {
    if a[k] != b[k] {
      return false
    }
  }
  true
}

///|
fn opt_eq(a : Int32?, b : Int32?) -> Bool {
  match (a, b) {
    (None, None) => true
    (Some(x), Some(y)) => x == y
    _ => false
  }
}

///|
/// Face restriction: fix coordinate `i` to `eps` and delete it.
/// Fails (`None`) when coordinate `i` is already fixed to the
/// opposite endpoint.
pub fn sc_face(n : Int32, code : Int32, i : Int32, eps : Int32) -> Int32? {
  let digit = @cubical.subcube_digit(code, i)
  if digit != 2 && digit != eps {
    return None
  }
  let digits = @cubical.subcube_digits(code, n)
  let out : Array[Int32] = []
  for k in 0..<n {
    if k != i {
      out.push(digits[k])
    }
  }
  Some(@cubical.subcube_code(out))
}

///|
/// Degeneracy: insert a free coordinate at position `i`.
pub fn sc_degen(n : Int32, code : Int32, i : Int32) -> Int32 {
  let digits = @cubical.subcube_digits(code, n)
  let out : Array[Int32] = []
  for k in 0..<(n + 1) {
    if k < i {
      out.push(digits[k])
    } else if k == i {
      out.push(2)
    } else {
      out.push(digits[k - 1])
    }
  }
  @cubical.subcube_code(out)
}

///|
/// Reversal: flip coordinate `i` (`0 <-> 1`, free stays free).
pub fn sc_rev(n : Int32, code : Int32, i : Int32) -> Int32 {
  let digits = @cubical.subcube_digits(code, n)
  let out : Array[Int32] = []
  for k in 0..<n {
    if k == i && digits[k] != 2 {
      out.push(1 - digits[k])
    } else {
      out.push(digits[k])
    }
  }
  @cubical.subcube_code(out)
}

///|
fn kleene_and(a : Int32, b : Int32) -> Int32 {
  if a == 0 || b == 0 {
    0
  } else if a == 1 && b == 1 {
    1
  } else {
    2
  }
}

///|
fn kleene_or(a : Int32, b : Int32) -> Int32 {
  if a == 1 || b == 1 {
    1
  } else if a == 0 && b == 0 {
    0
  } else {
    2
  }
}

///|
/// Connection: merge adjacent coordinates `i, i + 1` of a Kleene
/// assignment by `and` (the `Gamma^/\` connection) or by `or`
/// (the `Gamma\/` connection), reducing the arity by one.
pub fn sc_conn(digits : Array[Int32], i : Int32, is_and : Bool) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<digits.length() {
    if k < i {
      out.push(digits[k])
    } else if k == i {
      out.push(
        if is_and {
          kleene_and(digits[i], digits[i + 1])
        } else {
          kleene_or(digits[i], digits[i + 1])
        },
      )
    } else if k > i + 1 {
      out.push(digits[k])
    }
  }
  out
}

///|
pub fn check_small_cubical_operators() -> Bool {
  // Face-face, reversal, and degeneracy identities on the 2- and
  // 3-cubes, over every subcube.
  for n in [2, 3] {
    for code in 0..<@cubical.pow3(n) {
      for i in 0..<n {
        // Reversal is an involution.
        if sc_rev(n, sc_rev(n, code, i), i) != code {
          return false
        }
        for eps in [0, 1] {
          // A degenerate coordinate restricts back to the original
          // subcube at either endpoint.
          let deg = sc_degen(n, code, i)
          if !opt_eq(sc_face(n + 1, deg, i, eps), Some(code)) {
            return false
          }
          // Reversal commutes with faces in the expected way.
          if !opt_eq(
              sc_face(n, sc_rev(n, code, i), i, eps),
              sc_face(n, code, i, 1 - eps),
            ) {
            return false
          }
          for j in 0..<n {
            if j != i {
              if !opt_eq(
                  sc_face(n, sc_rev(n, code, i), j, eps),
                  match sc_face(n, code, j, eps) {
                    Some(c) =>
                      Some(sc_rev(n - 1, c, if j < i { i - 1 } else { i }))
                    None => None
                  },
                ) {
                return false
              }
            }
          }
        }
        // Face-face: for `i < j`, restricting `j` then `i` equals
        // restricting `i` then `j - 1`.
        for j in (i + 1)..<n {
          for eps in [0, 1] {
            for delta in [0, 1] {
              let lhs = match sc_face(n, code, j, eps) {
                Some(c1) => sc_face(n - 1, c1, i, delta)
                None => None
              }
              let rhs = match sc_face(n, code, i, delta) {
                Some(c1) => sc_face(n - 1, c1, j - 1, eps)
                None => None
              }
              if !opt_eq(lhs, rhs) {
                return false
              }
            }
          }
        }
        // Degeneracy-face shift identities.
        for j in 0..<n {
          for eps in [0, 1] {
            let deg = sc_degen(n, code, i)
            if j < i {
              let lhs = sc_face(n + 1, deg, j, eps)
              let rhs = match sc_face(n, code, j, eps) {
                Some(c) => Some(sc_degen(n - 1, c, i - 1))
                None => None
              }
              if !opt_eq(lhs, rhs) {
                return false
              }
            } else {
              let lhs = sc_face(n + 1, deg, j + 1, eps)
              let rhs = match sc_face(n, code, j, eps) {
                Some(c) => Some(sc_degen(n - 1, c, i))
                None => None
              }
              if !opt_eq(lhs, rhs) {
                return false
              }
            }
          }
        }
      }
    }
  }
  // Connection laws on every Kleene assignment of the 3-cube.
  for code in 0..<@cubical.pow3(3) {
    let digits = @cubical.subcube_digits(code, 3)
    for i in [0, 1] {
      let merged_and = sc_conn(digits, i, true)
      let merged_or = sc_conn(digits, i, false)
      if merged_and.length() != 2 || merged_or.length() != 2 {
        return false
      }
      // `(x /\ y)` at `x = 0` is `0` with `y` deleted; at `x = 1`
      // it is `y` with `x` deleted.  Dually for `\/`.
      if digits[i] == 0 {
        let expected : Array[Int32] = []
        for k in 0..<3 {
          if k < i {
            expected.push(digits[k])
          } else if k == i {
            expected.push(0)
          } else if k > i + 1 {
            expected.push(digits[k])
          }
        }
        if !int_arr_eq(merged_and, expected) {
          return false
        }
        let expected_or : Array[Int32] = []
        for k in 0..<2 {
          if k < i {
            expected_or.push(digits[k])
          } else {
            expected_or.push(digits[k + 1])
          }
        }
        if !int_arr_eq(merged_or, expected_or) {
          return false
        }
      }
      if digits[i] == 1 {
        let expected_and : Array[Int32] = []
        for k in 0..<2 {
          if k < i {
            expected_and.push(digits[k])
          } else {
            expected_and.push(digits[k + 1])
          }
        }
        if !int_arr_eq(merged_and, expected_and) {
          return false
        }
        let expected_or : Array[Int32] = []
        for k in 0..<3 {
          if k < i {
            expected_or.push(digits[k])
          } else if k == i {
            expected_or.push(1)
          } else if k > i + 1 {
            expected_or.push(digits[k])
          }
        }
        if !int_arr_eq(merged_or, expected_or) {
          return false
        }
      }
      // Idempotence of the connections on the diagonal.
      if digits[i] == digits[i + 1] && merged_and[i] != digits[i] {
        return false
      }
      if digits[i] == digits[i + 1] && merged_or[i] != digits[i] {
        return false
      }
    }
  }
  true
}

// ---------------------------------------------------------------------------
// Rewriting: decidability and confluence for dimension terms
// ---------------------------------------------------------------------------

///|
/// Syntactic equality of dimension terms.
pub fn dm_term_eq(a : Dim, b : Dim) -> Bool {
  match (a, b) {
    (Dim::DZero, Dim::DZero) => true
    (Dim::DOne, Dim::DOne) => true
    (Dim::DVar(x), Dim::DVar(y)) => x == y
    (Dim::DNeg(x), Dim::DNeg(y)) => dm_term_eq(x, y)
    (Dim::DAnd(x1, y1), Dim::DAnd(x2, y2)) =>
      dm_term_eq(x1, x2) && dm_term_eq(y1, y2)
    (Dim::DOr(x1, y1), Dim::DOr(x2, y2)) =>
      dm_term_eq(x1, x2) && dm_term_eq(y1, y2)
    _ => false
  }
}

///|
/// All one-step reducts of `t` under the DNF-directed rewrite
/// system: De Morgan push-down of negations, double-negation and
/// constant elimination, bounds / idempotence / absorption, and
/// distribution of `/\` over `\/`.
pub fn dm_step_all(t : Dim) -> Array[Dim] {
  let out : Array[Dim] = []
  match t {
    Dim::DZero | Dim::DOne | Dim::DVar(_) => ()
    Dim::DNeg(s) => {
      match s {
        Dim::DNeg(x) => out.push(x)
        Dim::DZero => out.push(Dim::DOne)
        Dim::DOne => out.push(Dim::DZero)
        Dim::DAnd(a, b) => out.push(Dim::DOr(Dim::DNeg(a), Dim::DNeg(b)))
        Dim::DOr(a, b) => out.push(Dim::DAnd(Dim::DNeg(a), Dim::DNeg(b)))
        _ => ()
      }
      for r in dm_step_all(s) {
        out.push(Dim::DNeg(r))
      }
    }
    Dim::DAnd(a, b) => {
      match b {
        Dim::DOne => out.push(a)
        Dim::DZero => out.push(Dim::DZero)
        Dim::DOr(y, z) => {
          out.push(Dim::DOr(Dim::DAnd(a, y), Dim::DAnd(a, z)))
          if dm_term_eq(a, y) || dm_term_eq(a, z) {
            out.push(a)
          }
        }
        _ => ()
      }
      match a {
        Dim::DOne => out.push(b)
        Dim::DZero => out.push(Dim::DZero)
        Dim::DOr(y, z) => out.push(Dim::DOr(Dim::DAnd(y, b), Dim::DAnd(z, b)))
        _ => ()
      }
      if dm_term_eq(a, b) {
        out.push(a)
      }
      for r in dm_step_all(a) {
        out.push(Dim::DAnd(r, b))
      }
      for r in dm_step_all(b) {
        out.push(Dim::DAnd(a, r))
      }
    }
    Dim::DOr(a, b) => {
      match b {
        Dim::DZero => out.push(a)
        Dim::DOne => out.push(Dim::DOne)
        Dim::DAnd(y, z) =>
          if dm_term_eq(a, y) || dm_term_eq(a, z) {
            out.push(a)
          }
        _ => ()
      }
      match a {
        Dim::DZero => out.push(b)
        Dim::DOne => out.push(Dim::DOne)
        Dim::DAnd(y, z) =>
          if dm_term_eq(b, y) || dm_term_eq(b, z) {
            out.push(b)
          }
        _ => ()
      }
      if dm_term_eq(a, b) {
        out.push(a)
      }
      for r in dm_step_all(a) {
        out.push(Dim::DOr(r, b))
      }
      for r in dm_step_all(b) {
        out.push(Dim::DOr(a, r))
      }
    }
  }
  out
}

///|
/// Deterministic (first-redex) normalisation with a step bound.
/// Returns the final term and whether an irreducible term was
/// reached within the bound.
pub fn dm_simplify(t : Dim) -> (Dim, Bool) {
  let mut cur = t
  let mut steps = 0
  while steps < 500 {
    let reducts = dm_step_all(cur)
    if reducts.length() == 0 {
      return (cur, true)
    }
    cur = reducts[0]
    steps = steps + 1
  }
  (cur, dm_step_all(cur).length() == 0)
}

///|
fn dm_sort_ints(xs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in xs {
    out.push(x)
  }
  for i in 0..<out.length() {
    for j in (i + 1)..<out.length() {
      if out[j] < out[i] {
        let tmp = out[i]
        out[i] = out[j]
        out[j] = tmp
      }
    }
  }
  out
}

///|
fn dm_clause_leq(a : Array[Int32], b : Array[Int32]) -> Bool {
  // Lexicographic order with shorter clauses first on a prefix.
  let n = if a.length() < b.length() { a.length() } else { b.length() }
  for k in 0..<n {
    if a[k] != b[k] {
      return a[k] < b[k]
    }
  }
  a.length() <= b.length()
}

///|
fn dm_is_subset(a : Array[Int32], b : Array[Int32]) -> Bool {
  for x in a {
    let mut found = false
    for y in b {
      if x == y {
        found = true
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
/// Canonical DNF, computed from scratch: negations are pushed to
/// atoms (literal `i` is coded `2i` positive, `2i + 1` negated),
/// literals and clauses are sorted and deduplicated, and clauses
/// subsumed by a smaller clause are dropped.  A clause containing
/// both `i` and `~i` is *kept*: the De Morgan algebra is not
/// Boolean, so such a clause is not bottom.
fn dm_join_clauses(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for x in a {
    out.push(x)
  }
  for y in b {
    out.push(y)
  }
  out
}

///|
fn dm_cross_clauses(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  for x in a {
    for y in b {
      let clause : Array[Int32] = []
      for l in x {
        clause.push(l)
      }
      for l in y {
        clause.push(l)
      }
      out.push(clause)
    }
  }
  out
}

///|
fn dm_dnf_go(r : Dim, neg : Bool) -> Array[Array[Int32]] {
  match r {
    Dim::DZero => if neg { [[]] } else { [] }
    Dim::DOne => if neg { [] } else { [[]] }
    Dim::DVar(i) => [[2 * i + (if neg { 1 } else { 0 })]]
    Dim::DNeg(s) => dm_dnf_go(s, !neg)
    Dim::DAnd(a, b) =>
      if neg {
        dm_join_clauses(dm_dnf_go(a, true), dm_dnf_go(b, true))
      } else {
        dm_cross_clauses(dm_dnf_go(a, false), dm_dnf_go(b, false))
      }
    Dim::DOr(a, b) =>
      if neg {
        dm_cross_clauses(dm_dnf_go(a, true), dm_dnf_go(b, true))
      } else {
        dm_join_clauses(dm_dnf_go(a, false), dm_dnf_go(b, false))
      }
  }
}

///|
pub fn dm_dnf_clauses(t : Dim) -> Array[Array[Int32]] {
  let raw = dm_dnf_go(t, false)
  // Canonicalise clauses: sort and dedup literals.
  let clauses : Array[Array[Int32]] = []
  for c in raw {
    let sorted = dm_sort_ints(c)
    let dedup : Array[Int32] = []
    for l in sorted {
      if dedup.length() == 0 || dedup[dedup.length() - 1] != l {
        dedup.push(l)
      }
    }
    clauses.push(dedup)
  }
  // Drop duplicated and subsumed clauses.
  let kept : Array[Array[Int32]] = []
  for c in clauses {
    let mut drop = false
    for d in clauses {
      if dm_is_subset(d, c) && !int_arr_eq(d, c) {
        drop = true
      }
    }
    if !drop {
      let mut dup = false
      for e in kept {
        if int_arr_eq(e, c) {
          dup = true
        }
      }
      if !dup {
        kept.push(c)
      }
    }
  }
  // Sort clauses canonically (insertion into order).
  let out : Array[Array[Int32]] = []
  for c in kept {
    out.push(c)
  }
  for i in 0..<out.length() {
    for j in (i + 1)..<out.length() {
      if dm_clause_leq(out[j], out[i]) && !int_arr_eq(out[j], out[i]) {
        let tmp = out[i]
        out[i] = out[j]
        out[j] = tmp
      }
    }
  }
  out
}

///|
/// Rebuild a dimension term from canonical DNF clauses.
pub fn dm_from_clauses(clauses : Array[Array[Int32]]) -> Dim {
  if clauses.length() == 0 {
    return Dim::DZero
  }
  let mut result = Dim::DZero
  let mut first = true
  for clause in clauses {
    let mut cterm = Dim::DOne
    let mut cfirst = true
    for lit in clause {
      let term = if lit % 2 == 0 {
        Dim::DVar(lit / 2)
      } else {
        Dim::DNeg(Dim::DVar(lit / 2))
      }
      if cfirst {
        cterm = term
        cfirst = false
      } else {
        cterm = Dim::DAnd(cterm, term)
      }
    }
    if first {
      result = cterm
      first = false
    } else {
      result = Dim::DOr(result, cterm)
    }
  }
  result
}

///|
/// Equality of dimension terms, decided by the from-scratch
/// canonical DNF above.
pub fn dm_decide_eq(a : Dim, b : Dim) -> Bool {
  let ca = dm_dnf_clauses(a)
  let cb = dm_dnf_clauses(b)
  if ca.length() != cb.length() {
    return false
  }
  for k in 0..<ca.length() {
    if !int_arr_eq(ca[k], cb[k]) {
      return false
    }
  }
  true
}

///|
pub fn check_confluence_decidability() -> Bool {
  let atoms = dm_atoms()
  let terms1 = dm_terms1()
  let pool = dm_pool()
  // The decision procedure agrees with the interval layer's
  // `dim_eq` oracle on all one-step terms, and with the rebuilt
  // normal form on the larger pool.
  for a in terms1 {
    for b in terms1 {
      if dm_decide_eq(a, b) != @face_bdd.dim_eq_demorgan(a, b) {
        return false
      }
    }
  }
  // Terms of depth two over the pool.
  let deep : Array[Dim] = []
  for a in pool {
    deep.push(Dim::DNeg(a))
    for b in pool {
      deep.push(Dim::DAnd(a, b))
      deep.push(Dim::DOr(a, b))
    }
  }
  for t in deep {
    // Normalisation is sound, idempotent, and decision-preserving.
    let nf = dm_from_clauses(dm_dnf_clauses(t))
    if !dm_decide_eq(nf, t) || !@face_bdd.dim_eq_demorgan(nf, t) {
      return false
    }
    if !dm_decide_eq(dm_from_clauses(dm_dnf_clauses(nf)), nf) {
      return false
    }
    // Deterministic rewriting terminates at an irreducible term
    // with the same DNF.
    let (simplified, terminated) = dm_simplify(t)
    if !terminated || !dm_decide_eq(simplified, t) {
      return false
    }
    // Local confluence: every pair of one-step reducts is joinable
    // (both decide equal to each other and to the original term),
    // i.e. all critical pairs of the finite system join.
    let reducts = dm_step_all(t)
    for r1 in reducts {
      if !dm_decide_eq(r1, t) {
        return false
      }
      for r2 in reducts {
        if !dm_decide_eq(r1, r2) {
          return false
        }
        let (j1, ok1) = dm_simplify(r1)
        let (j2, ok2) = dm_simplify(r2)
        if !ok1 || !ok2 || !dm_decide_eq(j1, j2) {
          return false
        }
      }
    }
  }
  // Sanity: distinct atoms and non-Boolean literals are decided
  // distinct / non-bottom.
  let i = atoms[2]
  if dm_decide_eq(i, atoms[3]) ||
    dm_decide_eq(Dim::DAnd(i, Dim::DNeg(i)), Dim::DZero) {
    return false
  }
  true
}
