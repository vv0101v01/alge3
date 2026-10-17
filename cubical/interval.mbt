///|
using @core {type Bits}

///|
/// Dimension terms of the cubical interval: the free De Morgan algebra on
/// the dimension variables.  `r, s ::= 0 | 1 | i | ~r | r /\ s | r \/ s`.
/// Note that this is *not* Boolean: `i /\ ~i` is not `0`, and the decision
/// procedure below (DNF in the free bounded distributive lattice with an
/// involution pushed to the atoms) respects that.
pub enum Dim {
  DZero
  DOne
  DVar(Int32)
  DNot(Dim)
  DAnd(Dim, Dim)
  DOr(Dim, Dim)
}

///|
/// Three-valued (Kleene) evaluation: 0 = false, 1 = true, 2 = free/unknown.
/// Assignments give one digit per variable in `{0, 1, 2}` where 2 means the
/// dimension is still free (the generic point of a subcube).
pub fn Dim::eval3(self : Dim, asg : Array[Int32]) -> Int32 {
  match self {
    DZero => 0
    DOne => 1
    DVar(i) => asg[i]
    DNot(r) =>
      match r.eval3(asg) {
        0 => 1
        1 => 0
        _ => 2
      }
    DAnd(a, b) => {
      let x = a.eval3(asg)
      let y = b.eval3(asg)
      if x == 0 || y == 0 {
        0
      } else if x == 1 && y == 1 {
        1
      } else {
        2
      }
    }
    DOr(a, b) => {
      let x = a.eval3(asg)
      let y = b.eval3(asg)
      if x == 1 || y == 1 {
        1
      } else if x == 0 && y == 0 {
        0
      } else {
        2
      }
    }
  }
}

///|
fn sort_unique_ints(xs : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in xs {
    let mut pos = out.length()
    for k in 0..<out.length() {
      if x < out[k] && pos == out.length() {
        pos = k
      }
    }
    let mut dup = false
    for y in out {
      if y == x {
        dup = true
      }
    }
    if !dup {
      out.push(x)
      // insertion at pos by rotating the tail
      let mut k = out.length() - 1
      while k > pos {
        out[k] = out[k - 1]
        k = k - 1
      }
      out[pos] = x
    }
  }
  out
}

///|
fn conj_subset(a : Array[Int32], b : Array[Int32]) -> Bool {
  // is a a subset of b (as sets of literals)?
  let mut ok = true
  for x in a {
    let mut found = false
    for y in b {
      if y == x {
        found = true
      }
    }
    if !found {
      ok = false
    }
  }
  ok
}

///|
fn conj_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  a.length() == b.length() && conj_subset(a, b)
}

///|
fn compare_conj(a : Array[Int32], b : Array[Int32]) -> Int32 {
  let m = if a.length() < b.length() { a.length() } else { b.length() }
  let mut r = 0
  for k in 0..<m {
    if r == 0 && a[k] != b[k] {
      r = if a[k] < b[k] { -1 } else { 1 }
    }
  }
  if r != 0 {
    r
  } else if a.length() == b.length() {
    0
  } else if a.length() < b.length() {
    -1
  } else {
    1
  }
}

///|
/// Canonical DNF: duplicate conjunctions removed, absorption applied
/// (`x \/ (x /\ y) = x`, so a conjunction that strictly contains another is
/// dropped), and conjunctions sorted lexicographically.  Two dimension
/// terms are equal in the free De Morgan algebra iff their canonical DNFs
/// coincide.
fn dnf_canon(terms : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let dedup : Array[Array[Int32]] = []
  for t in terms {
    let st = sort_unique_ints(t)
    let mut seen = false
    for u in dedup {
      if conj_eq(u, st) {
        seen = true
      }
    }
    if !seen {
      dedup.push(st)
    }
  }
  let kept : Array[Array[Int32]] = []
  for t in dedup {
    let mut absorbed = false
    for u in dedup {
      if !conj_eq(u, t) && conj_subset(u, t) {
        absorbed = true
      }
    }
    if !absorbed {
      kept.push(t)
    }
  }
  // insertion sort
  let out : Array[Array[Int32]] = []
  for t in kept {
    out.push(t)
    let mut k = out.length() - 1
    while k > 0 && compare_conj(out[k - 1], out[k]) > 0 {
      let tmp = out[k - 1]
      out[k - 1] = out[k]
      out[k] = tmp
      k = k - 1
    }
  }
  out
}

///|
fn dnf_and(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let terms : Array[Array[Int32]] = []
  for x in a {
    for y in b {
      let m : Array[Int32] = []
      for v in x {
        m.push(v)
      }
      for v in y {
        m.push(v)
      }
      terms.push(m)
    }
  }
  dnf_canon(terms)
}

///|
fn dnf_or(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let terms : Array[Array[Int32]] = []
  for x in a {
    terms.push(x)
  }
  for y in b {
    terms.push(y)
  }
  dnf_canon(terms)
}

///|
/// DNF of a dimension term; `neg` tracks a pending reversal, which is
/// pushed to the atoms by the De Morgan laws.  A literal for variable `i`
/// is encoded `2i` (positive) or `2i + 1` (negated).
fn dnf_of(r : Dim, neg : Bool) -> Array[Array[Int32]] {
  match r {
    DZero => if neg { [[]] } else { [] }
    DOne => if neg { [] } else { [[]] }
    DVar(i) => [[2 * i + (if neg { 1 } else { 0 })]]
    DNot(s) => dnf_of(s, !neg)
    DAnd(a, b) =>
      if neg {
        dnf_or(dnf_of(a, true), dnf_of(b, true))
      } else {
        dnf_and(dnf_of(a, false), dnf_of(b, false))
      }
    DOr(a, b) =>
      if neg {
        dnf_and(dnf_of(a, true), dnf_of(b, true))
      } else {
        dnf_or(dnf_of(a, false), dnf_of(b, false))
      }
  }
}

///|
/// The canonical DNF of a dimension term (list of conjunctions of literals).
pub fn Dim::dnf(self : Dim) -> Array[Array[Int32]] {
  dnf_of(self, false)
}

///|
/// Decidable equality of dimension terms in the free De Morgan algebra.
pub fn dim_eq(a : Dim, b : Dim) -> Bool {
  let da = a.dnf()
  let db = b.dnf()
  if da.length() != db.length() {
    return false
  }
  let mut ok = true
  for k in 0..<da.length() {
    if !conj_eq(da[k], db[k]) {
      ok = false
    }
  }
  ok
}

///|
/// `3^k`: the number of subcubes (faces) of the `k`-cube, since each
/// coordinate of a subcube is `0`, `1` or free (`*`, digit 2).
pub fn pow3(k : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<k {
    r = r * 3
  }
  r
}

///|
/// The `k`-th ternary digit of a subcube code (0, 1, or 2 = free).
pub fn subcube_digit(code : Int32, k : Int32) -> Int32 {
  code / pow3(k) % 3
}

///|
pub fn subcube_digits(code : Int32, n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for k in 0..<n {
    out.push(subcube_digit(code, k))
  }
  out
}

///|
pub fn subcube_code(digits : Array[Int32]) -> Int32 {
  let mut c = 0
  for k in 0..<digits.length() {
    c = c + digits[k] * pow3(k)
  }
  c
}

///|
/// The subcube code obtained by forcing coordinate `dim` to `v`.
pub fn subcube_set_digit(code : Int32, dim : Int32, v : Int32) -> Int32 {
  code + (v - subcube_digit(code, dim)) * pow3(dim)
}

///|
/// The generic (top-dimensional) subcube: every coordinate free.
pub fn generic_cube(n : Int32) -> Int32 {
  pow3(n) - 1
}

///|
/// The face `dim = eps` with all other coordinates free.
pub fn face_cube(n : Int32, dim : Int32, eps : Int32) -> Int32 {
  subcube_set_digit(generic_cube(n), dim, eps)
}

///|
/// Is `face` a subcube of `big`?  (Face relation of the cube category,
/// restricted to face maps.)
pub fn is_subface(face : Int32, big : Int32, n : Int32) -> Bool {
  let mut ok = true
  for k in 0..<n {
    let b = subcube_digit(big, k)
    let f = subcube_digit(face, k)
    if b != 2 && b != f {
      ok = false
    }
  }
  ok
}

///|
/// Intersection of two subcubes, or `-1` when they are disjoint.
pub fn meet_cube(a : Int32, b : Int32, n : Int32) -> Int32 {
  let digits : Array[Int32] = []
  let mut disjoint = false
  for k in 0..<n {
    let x = subcube_digit(a, k)
    let y = subcube_digit(b, k)
    if x == 2 {
      digits.push(y)
    } else if y == 2 || x == y {
      digits.push(x)
    } else {
      disjoint = true
      digits.push(0)
    }
  }
  if disjoint {
    -1
  } else {
    subcube_code(digits)
  }
}

///|
/// Cofibrations (face formulas): the propositions of the face lattice
/// generated by equations `r = eps` between dimension terms and endpoints.
pub enum Cof {
  CTop
  CBot
  CEq(Dim, Int32)
  CAnd(Cof, Cof)
  COr(Cof, Cof)
}

///|
/// The face cofibration `(dim = eps)`.
pub fn face_cof(dim : Int32, eps : Int32) -> Cof {
  CEq(DVar(dim), eps)
}

///|
/// Does the cofibration hold on the subcube with the given digits?  An
/// equation `r = eps` holds on a subcube iff `r` is forced to the constant
/// `eps` there (Kleene evaluation returns exactly `eps`, not "free").
pub fn Cof::holds(self : Cof, digits : Array[Int32]) -> Bool {
  match self {
    CTop => true
    CBot => false
    CEq(r, eps) => r.eval3(digits) == eps
    CAnd(a, b) => a.holds(digits) && b.holds(digits)
    COr(a, b) => a.holds(digits) || b.holds(digits)
  }
}

///|
pub fn Cof::holds_code(self : Cof, code : Int32, n : Int32) -> Bool {
  self.holds(subcube_digits(code, n))
}

///|
/// The extent of a cofibration: the bitset of subcubes of the `n`-cube on
/// which it holds.  Extents are downward closed (closed under subfaces),
/// and two cofibrations are equal iff their extents are equal.
pub fn Cof::extent(self : Cof, n : Int32) -> Bits {
  let total = pow3(n)
  let bits = Bits::new(total)
  for code in 0..<total {
    if self.holds_code(code, n) {
      bits.set(code)
    }
  }
  bits
}

///|
/// Decidable entailment in the face lattice: `phi <= psi` iff the extent
/// of `phi` is contained in the extent of `psi`.
pub fn cof_entails(phi : Cof, psi : Cof, n : Int32) -> Bool {
  let a = phi.extent(n)
  let b = psi.extent(n)
  let mut ok = true
  for code in 0..<pow3(n) {
    if a.get(code) && !b.get(code) {
      ok = false
    }
  }
  ok
}

///|
pub fn cof_equiv(phi : Cof, psi : Cof, n : Int32) -> Bool {
  phi.extent(n).same(psi.extent(n))
}

///|
pub fn cof_is_top(phi : Cof, n : Int32) -> Bool {
  phi.extent(n).weight() == pow3(n)
}

///|
pub fn cof_is_bot(phi : Cof, n : Int32) -> Bool {
  phi.extent(n).is_zero()
}

///|
/// Number of subcubes in the extent of `phi`.
pub fn cof_extent_size(phi : Cof, n : Int32) -> Int32 {
  phi.extent(n).weight()
}

///|
/// The maximal subcubes in the extent of `phi`: a finite set of faces whose
/// union is the extent.  Partial elements (systems) are presented by giving
/// one component on each of these maximal faces.
pub fn cof_maximal_faces(phi : Cof, n : Int32) -> Array[Int32] {
  let ext = phi.extent(n)
  let out : Array[Int32] = []
  for code in 0..<pow3(n) {
    if ext.get(code) {
      let mut maximal = true
      for other in 0..<pow3(n) {
        if other != code && ext.get(other) && is_subface(code, other, n) {
          maximal = false
        }
      }
      if maximal {
        out.push(code)
      }
    }
  }
  out
}

///|
/// Endpoint substitution in a dimension term: replace `DVar(dim)` by the
/// constant `eps`, leaving other variables untouched.  This is the
/// syntactic counterpart of restricting a cube to a face.
pub fn dim_subst_endpoint(r : Dim, dim : Int32, eps : Int32) -> Dim {
  match r {
    DZero => DZero
    DOne => DOne
    DVar(i) =>
      if i == dim {
        if eps == 0 {
          DZero
        } else {
          DOne
        }
      } else {
        DVar(i)
      }
    DNot(s) => DNot(dim_subst_endpoint(s, dim, eps))
    DAnd(a, b) =>
      DAnd(dim_subst_endpoint(a, dim, eps), dim_subst_endpoint(b, dim, eps))
    DOr(a, b) =>
      DOr(dim_subst_endpoint(a, dim, eps), dim_subst_endpoint(b, dim, eps))
  }
}

///|
/// Endpoint substitution in a cofibration, with the constant cases folded:
/// if the equation becomes constant it is replaced by `⊤` or `⊥`.
pub fn cof_subst_endpoint(phi : Cof, dim : Int32, eps : Int32) -> Cof {
  match phi {
    CTop => CTop
    CBot => CBot
    CEq(r, e) =>
      match dim_subst_endpoint(r, dim, eps) {
        DZero => if e == 0 { CTop } else { CBot }
        DOne => if e == 1 { CTop } else { CBot }
        s => CEq(s, e)
      }
    CAnd(a, b) =>
      CAnd(cof_subst_endpoint(a, dim, eps), cof_subst_endpoint(b, dim, eps))
    COr(a, b) =>
      COr(cof_subst_endpoint(a, dim, eps), cof_subst_endpoint(b, dim, eps))
  }
}

///|
/// Conjunction of cofibrations (meet in the face lattice).
pub fn Cof::conj(self : Cof, other : Cof) -> Cof {
  CAnd(self, other)
}

///|
/// Disjunction of cofibrations (join in the face lattice).
pub fn Cof::disj(self : Cof, other : Cof) -> Cof {
  COr(self, other)
}
