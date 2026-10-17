///|
/// Finite maps between finite sets `Fin n`, represented by their graphs
/// as arrays.  Elements of every finite type below are coded by `Int32`.

///|
pub fn fn_id(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<n {
    out.push(i)
  }
  out
}

///|
/// Composition `g ∘ f` (apply `f`, then `g`).
pub fn fn_comp(f : Array[Int32], g : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for x in 0..<f.length() {
    out.push(g[f[x]])
  }
  out
}

///|
pub fn fn_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut ok = true
  for i in 0..<a.length() {
    if a[i] != b[i] {
      ok = false
    }
  }
  ok
}

///|
/// The inverse of `f : Fin (f.length) -> Fin cod`, if it is a bijection.
/// For finite sets, `isEquiv f` is decidable and equivalent to `f` being
/// a bijection; this is the algorithmic content of that fact.
pub fn fn_inv(f : Array[Int32], cod : Int32) -> Array[Int32]? {
  if f.length() != cod {
    return None
  }
  let inv = Array::make(cod, -1)
  for x in 0..<f.length() {
    let y = f[x]
    if y < 0 || y >= cod || inv[y] != -1 {
      return None
    }
    inv[y] = x
  }
  Some(inv)
}

///|
pub fn fn_is_bijection(f : Array[Int32], cod : Int32) -> Bool {
  match fn_inv(f, cod) {
    Some(_) => true
    None => false
  }
}

///|
/// An isomorphism (equivalence) of finite sets: a map with a two-sided
/// inverse.  For 0-types this is exactly an equivalence `Fin dom ≃ Fin cod`.
pub struct Iso {
  dom : Int32
  cod : Int32
  fwd : Array[Int32]
  bwd : Array[Int32]
}

///|
pub fn Iso::new(
  dom : Int32,
  cod : Int32,
  fwd : Array[Int32],
  bwd : Array[Int32],
) -> Iso {
  Iso::{ dom, cod, fwd, bwd, }
}

///|
pub fn Iso::id(n : Int32) -> Iso {
  Iso::{ dom: n, cod: n, fwd: fn_id(n), bwd: fn_id(n), }
}

///|
/// Build an isomorphism from a single map by computing its inverse.
pub fn iso_of_fn(f : Array[Int32], dom : Int32, cod : Int32) -> Iso? {
  match fn_inv(f, cod) {
    Some(g) => Some(Iso::{ dom, cod, fwd: f, bwd: g, })
    None => None
  }
}

///|
pub fn Iso::check(self : Iso) -> Bool {
  self.fwd.length() == self.dom &&
  self.bwd.length() == self.cod &&
  fn_eq(fn_comp(self.fwd, self.bwd), fn_id(self.dom)) &&
  fn_eq(fn_comp(self.bwd, self.fwd), fn_id(self.cod))
}

///|
/// Composition of equivalences: `other ∘ self`.
pub fn Iso::then(self : Iso, other : Iso) -> Iso {
  Iso::{
    dom: self.dom,
    cod: other.cod,
    fwd: fn_comp(self.fwd, other.fwd),
    bwd: fn_comp(other.bwd, self.bwd),
  }
}

///|
pub fn Iso::inv(self : Iso) -> Iso {
  Iso::{ dom: self.cod, cod: self.dom, fwd: self.bwd, bwd: self.fwd, }
}

///|
pub fn Iso::apply(self : Iso, x : Int32) -> Int32 {
  self.fwd[x]
}

///|
pub fn Iso::apply_inv(self : Iso, y : Int32) -> Int32 {
  self.bwd[y]
}

///|
/// A finite cubical type over `n` dimensions: a diagram on the face poset
/// of the `n`-cube.  For every subcube `σ` a finite set of cardinality
/// `card[σ]` (elements coded `0 ..< card[σ]`), and for every face inclusion
/// `τ ⊆ σ` a restriction map `res[σ][τ]`.  This is a finite presheaf on the
/// face category; an element in context is an element over the generic
/// subcube, all of whose faces are its restrictions.
pub struct CubeTy {
  n : Int32
  card : Array[Int32]
  res : Array[Array[Int32]]
}

///|
pub fn CubeTy::new(
  n : Int32,
  card : Array[Int32],
  res : Array[Array[Int32]],
) -> CubeTy {
  CubeTy::{ n, card, res, }
}

///|
pub fn CubeTy::stages(self : CubeTy) -> Int32 {
  pow3(self.n)
}

///|
pub fn CubeTy::res_fn(self : CubeTy, big : Int32, face : Int32) -> Array[Int32] {
  self.res[big * self.stages() + face]
}

///|
/// Restrict the cube `x` over `big` to the face `face ⊆ big`.
pub fn CubeTy::restrict(
  self : CubeTy,
  big : Int32,
  face : Int32,
  x : Int32,
) -> Int32 {
  self.res_fn(big, face)[x]
}

///|
/// Cardinality over the generic subcube: the number of elements in context.
pub fn CubeTy::generic_card(self : CubeTy) -> Int32 {
  self.card[generic_cube(self.n)]
}

///|
/// Verify the presheaf laws: restriction along the identity is the
/// identity, and restriction is functorial (`x|τ = (x|σ)|τ` for
/// `τ ⊆ σ ⊆ ρ`).  Exhaustive over all elements and face inclusions.
pub fn CubeTy::check(self : CubeTy) -> Bool {
  let total = self.stages()
  let n = self.n
  for s in 0..<total {
    if self.card[s] < 0 || !fn_eq(self.res_fn(s, s), fn_id(self.card[s])) {
      return false
    }
  }
  for big in 0..<total {
    for mid in 0..<total {
      if is_subface(mid, big, n) {
        for face in 0..<total {
          if is_subface(face, mid, n) {
            for x in 0..<self.card[big] {
              let y = self.restrict(big, mid, x)
              if y < 0 || y >= self.card[mid] {
                return false
              }
              if self.restrict(mid, face, y) != self.restrict(big, face, x) {
                return false
              }
            }
          }
        }
      }
    }
  }
  true
}

///|
fn build_ty(
  n : Int32,
  card : Array[Int32],
  mk : (Int32, Int32) -> Array[Int32],
) -> CubeTy {
  let total = pow3(n)
  let res : Array[Array[Int32]] = []
  for big in 0..<total {
    for face in 0..<total {
      if is_subface(face, big, n) {
        res.push(mk(big, face))
      } else {
        res.push([])
      }
    }
  }
  CubeTy::{ n, card, res, }
}

///|
/// The constant (discrete) type on `Fin c`: every stage is `Fin c` and
/// every restriction is the identity.  Cubes in a discrete type are
/// constant, so its path types are the equality propositions.
pub fn const_ty(n : Int32, c : Int32) -> CubeTy {
  let card : Array[Int32] = []
  for _ in 0..<pow3(n) {
    card.push(c)
  }
  build_ty(n, card, fn(_big, _face) { fn_id(c) })
}

///|
/// Pointwise product of cubical types.  The element `(a, b)` at stage `σ`
/// is coded `a * card_Y(σ) + b`.
pub fn prod_ty(x : CubeTy, y : CubeTy) -> CubeTy {
  let n = x.n
  let card : Array[Int32] = []
  for s in 0..<pow3(n) {
    card.push(x.card[s] * y.card[s])
  }
  build_ty(n, card, fn(big, face) {
    let yb = y.card[big]
    let yf = y.card[face]
    let out : Array[Int32] = []
    for v in 0..<(x.card[big] * yb) {
      let a = v / yb
      let b = v % yb
      out.push(x.restrict(big, face, a) * yf + y.restrict(big, face, b))
    }
    out
  })
}

///|
/// Dependent sum over a constant finite base: `Σ (s : Fin m), fibers[s]`.
/// The element `(s, v)` at stage `σ` is coded by the cumulative offset of
/// the fibers at `σ`, plus `v`.
pub fn sigma_const_ty(fibers : Array[CubeTy]) -> CubeTy {
  let n = fibers[0].n
  let card : Array[Int32] = []
  for s in 0..<pow3(n) {
    let mut sum = 0
    for f in fibers {
      sum = sum + f.card[s]
    }
    card.push(sum)
  }
  build_ty(n, card, fn(big, face) {
    let out : Array[Int32] = []
    let mut off_big = 0
    let mut off_face = 0
    for f in fibers {
      for v in 0..<f.card[big] {
        out.push(off_face + f.restrict(big, face, v))
      }
      off_big = off_big + f.card[big]
      off_face = off_face + f.card[face]
      ignore(off_big)
    }
    out
  })
}

///|
/// Dependent product over a constant finite base: `Π (s : Fin m), fibers[s]`.
/// Elements at stage `σ` are tuples coded in mixed radix (component `0` is
/// the least significant digit).
pub fn pi_const_ty(fibers : Array[CubeTy]) -> CubeTy {
  let n = fibers[0].n
  let card : Array[Int32] = []
  for s in 0..<pow3(n) {
    let mut p = 1
    for f in fibers {
      p = p * f.card[s]
    }
    card.push(p)
  }
  build_ty(n, card, fn(big, face) {
    let mut total = 1
    for f in fibers {
      total = total * f.card[big]
    }
    let out : Array[Int32] = []
    for code in 0..<total {
      let mut rest = code
      let mut acc = 0
      let mut place = 1
      for f in fibers {
        let digit = rest % f.card[big]
        rest = rest / f.card[big]
        acc = acc + f.restrict(big, face, digit) * place
        place = place * f.card[face]
      }
      out.push(acc)
    }
    out
  })
}

///|
/// Extend a type over `n` dimensions constantly along a fresh dimension
/// (the new last coordinate, index `n`).  This is the degeneracy/pullback
/// along the projection, used for `hcomp` and path types.
pub fn extend_ty(x : CubeTy) -> CubeTy {
  let old = pow3(x.n)
  let card : Array[Int32] = []
  for s in 0..<pow3(x.n + 1) {
    card.push(x.card[s % old])
  }
  build_ty(x.n + 1, card, fn(big, face) { x.res_fn(big % old, face % old) })
}

///|
fn insert_digit_code(
  code : Int32,
  n_new : Int32,
  dim : Int32,
  v : Int32,
) -> Int32 {
  let digits = subcube_digits(code, n_new)
  let out : Array[Int32] = []
  for k in 0..<(n_new + 1) {
    if k < dim {
      out.push(digits[k])
    } else if k == dim {
      out.push(v)
    } else {
      out.push(digits[k - 1])
    }
  }
  subcube_code(out)
}

///|
/// The face of a cubical type at `dim = eps`: the diagram over the
/// remaining `n - 1` dimensions obtained by restricting every stage.
/// For a line of types (`n = 1`) this recovers its endpoint types.
pub fn face_ty(x : CubeTy, dim : Int32, eps : Int32) -> CubeTy {
  let nn = x.n - 1
  let card : Array[Int32] = []
  for s in 0..<pow3(nn) {
    card.push(x.card[insert_digit_code(s, nn, dim, eps)])
  }
  build_ty(nn, card, fn(big, face) {
    x.res_fn(
      insert_digit_code(big, nn, dim, eps),
      insert_digit_code(face, nn, dim, eps),
    )
  })
}

///|
fn map_digits_code(
  code : Int32,
  n : Int32,
  f : (Array[Int32]) -> Array[Int32],
) -> Int32 {
  subcube_code(f(subcube_digits(code, n)))
}

///|
fn reindex_ty(x : CubeTy, pi : (Int32) -> Int32) -> CubeTy {
  let card : Array[Int32] = []
  for s in 0..<pow3(x.n) {
    card.push(x.card[pi(s)])
  }
  build_ty(x.n, card, fn(big, face) { x.res_fn(pi(big), pi(face)) })
}

///|
/// Reverse a dimension (`i ↦ ~i`): swap digits 0 and 1 in coordinate
/// `dim`.  Applied to a line of types this is path symmetry in the
/// universe; applied inside a type it is path reversal.
pub fn reverse_ty(x : CubeTy, dim : Int32) -> CubeTy {
  reindex_ty(x, fn(code) {
    map_digits_code(code, x.n, fn(digits) {
      let out : Array[Int32] = []
      for k in 0..<digits.length() {
        if k == dim && digits[k] != 2 {
          out.push(1 - digits[k])
        } else {
          out.push(digits[k])
        }
      }
      out
    })
  })
}

///|
/// Swap two coordinates of the ambient cube.
pub fn swap_dims_ty(x : CubeTy, d1 : Int32, d2 : Int32) -> CubeTy {
  reindex_ty(x, fn(code) {
    map_digits_code(code, x.n, fn(digits) {
      let out : Array[Int32] = []
      for k in 0..<digits.length() {
        if k == d1 {
          out.push(digits[d2])
        } else if k == d2 {
          out.push(digits[d1])
        } else {
          out.push(digits[k])
        }
      }
      out
    })
  })
}

///|
/// Validate Glue data: on every stage `σ` in the extent of `phi`,
/// `e[σ] : T(σ) -> A(σ)` must be a bijection, natural in `σ`
/// (`e_τ ∘ res^σ_τ = res^σ_τ ∘ e_σ`).  In general cubical type theory `e`
/// is an equivalence; for finite types naturality of the inverse data is
/// exactly the extra coherence needed for `comp` in the Glue type.
pub fn check_glue_data(
  phi : Cof,
  t : CubeTy,
  a : CubeTy,
  e : Array[Array[Int32]],
) -> Bool {
  let n = a.n
  let total = pow3(n)
  for s in 0..<total {
    if phi.holds_code(s, n) {
      if e[s].length() != t.card[s] || !fn_is_bijection(e[s], a.card[s]) {
        return false
      }
    }
  }
  for big in 0..<total {
    if phi.holds_code(big, n) {
      for face in 0..<total {
        if is_subface(face, big, n) && phi.holds_code(face, n) {
          for x in 0..<t.card[big] {
            if e[face][t.restrict(big, face, x)] !=
              a.restrict(big, face, e[big][x]) {
              return false
            }
          }
        }
      }
    }
  }
  true
}

///|
/// The Glue type `Glue [phi ↦ (T, e)] A`.  At a stage where `phi` holds it
/// *is* `T` (strictly); elsewhere it is `A`.  Restriction from a stage
/// outside the extent to a face inside it is twisted by `e^{-1}`, which is
/// what makes transport across the glued face compute to `e`.
/// Assumes `check_glue_data(phi, t, a, e)`.
pub fn glue_ty(
  phi : Cof,
  t : CubeTy,
  a : CubeTy,
  e : Array[Array[Int32]],
) -> CubeTy {
  let n = a.n
  let card : Array[Int32] = []
  for s in 0..<pow3(n) {
    if phi.holds_code(s, n) {
      card.push(t.card[s])
    } else {
      card.push(a.card[s])
    }
  }
  build_ty(n, card, fn(big, face) {
    if phi.holds_code(big, n) {
      t.res_fn(big, face)
    } else if !phi.holds_code(face, n) {
      a.res_fn(big, face)
    } else {
      let inv = match fn_inv(e[face], a.card[face]) {
        Some(g) => g
        None => fn_id(a.card[face])
      }
      fn_comp(a.res_fn(big, face), inv)
    }
  })
}

///|
/// The path type `Path_X a b` for `a, b` elements of `x` in context
/// (elements over the generic subcube).  Its cubes at stage `σ` are the
/// cubes of `x` over `σ × I` whose two end faces are `a|σ` and `b|σ`:
/// paths are literally lines, and `Path` is computed by filtering the
/// finite set of one-dimension-higher cubes.
pub fn path_ty(x : CubeTy, a : Int32, b : Int32) -> CubeTy {
  let y = extend_ty(x)
  let base = pow3(x.n)
  let gen = generic_cube(x.n)
  let elems : Array[Array[Int32]] = []
  let card : Array[Int32] = []
  for s in 0..<base {
    let mid = s + 2 * base
    let sa = x.restrict(gen, s, a)
    let sb = x.restrict(gen, s, b)
    let list : Array[Int32] = []
    for z in 0..<y.card[mid] {
      if y.restrict(mid, s, z) == sa && y.restrict(mid, s + base, z) == sb {
        list.push(z)
      }
    }
    card.push(list.length())
    elems.push(list)
  }
  build_ty(x.n, card, fn(big, face) {
    let out : Array[Int32] = []
    for z in elems[big] {
      let w = y.restrict(big + 2 * base, face + 2 * base, z)
      let mut idx = 0
      for k in 0..<elems[face].length() {
        if elems[face][k] == w {
          idx = k
        }
      }
      out.push(idx)
    }
    out
  })
}

///|
/// A stage-wise isomorphism of cubical types: bijections at every stage,
/// natural with respect to all restrictions, with a two-sided inverse.
/// Two lines of types related by a `TyIso` define the same path in the
/// finite universe.
pub struct TyIso {
  fwd : Array[Array[Int32]]
  bwd : Array[Array[Int32]]
}

///|
pub fn TyIso::new(
  fwd : Array[Array[Int32]],
  bwd : Array[Array[Int32]],
) -> TyIso {
  TyIso::{ fwd, bwd, }
}

///|
/// The identity stage-wise isomorphism.
pub fn ty_iso_id(x : CubeTy) -> TyIso {
  let fwd : Array[Array[Int32]] = []
  let bwd : Array[Array[Int32]] = []
  for s in 0..<pow3(x.n) {
    fwd.push(fn_id(x.card[s]))
    bwd.push(fn_id(x.card[s]))
  }
  TyIso::{ fwd, bwd, }
}

///|
pub fn check_ty_iso(x : CubeTy, y : CubeTy, iso : TyIso) -> Bool {
  if x.n != y.n {
    return false
  }
  let total = pow3(x.n)
  for s in 0..<total {
    if !fn_eq(fn_comp(iso.fwd[s], iso.bwd[s]), fn_id(x.card[s])) {
      return false
    }
    if !fn_eq(fn_comp(iso.bwd[s], iso.fwd[s]), fn_id(y.card[s])) {
      return false
    }
  }
  for big in 0..<total {
    for face in 0..<total {
      if is_subface(face, big, x.n) {
        for v in 0..<x.card[big] {
          if y.restrict(big, face, iso.fwd[big][v]) !=
            iso.fwd[face][x.restrict(big, face, v)] {
            return false
          }
        }
        for v in 0..<y.card[big] {
          if x.restrict(big, face, iso.bwd[big][v]) !=
            iso.bwd[face][y.restrict(big, face, v)] {
            return false
          }
        }
      }
    }
  }
  true
}

///|
fn int_pow(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<exp {
    r = r * base
  }
  r
}

///|
/// Are all restriction maps bijections?  Lines produced by `ua`, Glue and
/// the constant types have this property: they are the lines along which
/// transport is an equivalence at every stage.
pub fn all_res_bijective(x : CubeTy) -> Bool {
  let total = pow3(x.n)
  for big in 0..<total {
    for face in 0..<total {
      if is_subface(face, big, x.n) &&
        !fn_is_bijection(x.res_fn(big, face), x.card[face]) {
        return false
      }
    }
  }
  true
}

///|
/// The function type `A -> B` for a domain `A` all of whose restrictions
/// are bijective.  At stage `σ` an element is a function `A(σ) -> B(σ)`,
/// coded by its table in mixed radix; restriction is conjugation:
/// `f|τ = res_B ∘ f ∘ (res_A)^{-1}`.  Transport in this type along a line
/// is therefore exactly "transport of structure": operations are carried
/// across equivalences by conjugation, and along `ua(e)` this computes.
pub fn fun_ty(a : CubeTy, b : CubeTy) -> CubeTy {
  let n = a.n
  let card : Array[Int32] = []
  for s in 0..<pow3(n) {
    card.push(int_pow(b.card[s], a.card[s]))
  }
  build_ty(n, card, fn(big, face) {
    let inv_a = match fn_inv(a.res_fn(big, face), a.card[face]) {
      Some(g) => g
      None => fn_id(a.card[face])
    }
    let total = int_pow(b.card[big], a.card[big])
    let out : Array[Int32] = []
    for code in 0..<total {
      // decode the table of f at stage `big`
      let digits : Array[Int32] = []
      let mut rest = code
      for _ in 0..<a.card[big] {
        digits.push(rest % b.card[big])
        rest = rest / b.card[big]
      }
      // conjugate and re-encode at stage `face`
      let mut acc = 0
      let mut place = 1
      for af in 0..<a.card[face] {
        let v = b.restrict(big, face, digits[inv_a[af]])
        acc = acc + v * place
        place = place * b.card[face]
      }
      out.push(acc)
    }
    out
  })
}
