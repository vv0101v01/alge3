///|
// Path types and local complementedness.
//
// In the finite cubical model a type over `n` dimensions is a
// presheaf on the face poset of the `n`-cube: a finite set at every
// subcube (stage) and restriction maps along face inclusions.  A
// stage-wise subset is a *subobject* when it is stable under
// restriction, and it is *locally complemented* (a complemented /
// decidable subobject, with a characteristic map to the subobject
// classifier at every stage) when both it and its stage-wise
// complement are subobjects.  Complementedness is a local,
// stage-by-stage property, and for finite presheaves it is
// decidable by enumerating the stage-wise subsets.
//
// This file implements a small self-contained presheaf model
// (`MiniTy`) mirroring `@cubical.CubeTy`, computes path types by
// filtering higher cubes (the same algorithm as
// `@cubical.path_ty`, cross-checked against it), and decides
// local complementedness of stage-wise subsets exhaustively.

///|
/// A finite presheaf on the face poset of the `n`-cube:
/// `card[sigma]` elements at stage `sigma`, and `res[big][face]`
/// the restriction function (as an array) along `face <= big`.
pub(all) struct MiniTy {
  n : Int32
  card : Array[Int32]
  res : Array[Array[Int32]]
}

///|
fn mini_build(
  n : Int32,
  card : Array[Int32],
  mk : (Int32, Int32) -> Array[Int32],
) -> MiniTy {
  let total = @cubical.pow3(n)
  let res : Array[Array[Int32]] = []
  for big in 0..<total {
    for face in 0..<total {
      if @cubical.is_subface(face, big, n) {
        res.push(mk(big, face))
      } else {
        res.push([])
      }
    }
  }
  MiniTy::{ n, card, res, }
}

///|
pub fn MiniTy::mini_res_fn(
  self : MiniTy,
  big : Int32,
  face : Int32,
) -> Array[Int32] {
  self.res[big * @cubical.pow3(self.n) + face]
}

///|
pub fn MiniTy::mini_restrict(
  self : MiniTy,
  big : Int32,
  face : Int32,
  x : Int32,
) -> Int32 {
  self.mini_res_fn(big, face)[x]
}

///|
/// Presheaf laws, checked exhaustively (identity and functoriality
/// of restriction).
pub fn MiniTy::mini_check(self : MiniTy) -> Bool {
  let total = @cubical.pow3(self.n)
  for s in 0..<total {
    if self.card[s] < 0 {
      return false
    }
    let id = self.mini_res_fn(s, s)
    if id.length() != self.card[s] {
      return false
    }
    for x in 0..<self.card[s] {
      if id[x] != x {
        return false
      }
    }
  }
  for big in 0..<total {
    for mid in 0..<total {
      if @cubical.is_subface(mid, big, self.n) {
        for face in 0..<total {
          if @cubical.is_subface(face, mid, self.n) {
            for x in 0..<self.card[big] {
              let y = self.mini_restrict(big, mid, x)
              if y < 0 || y >= self.card[mid] {
                return false
              }
              if self.mini_restrict(mid, face, y) !=
                self.mini_restrict(big, face, x) {
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
/// The constant (discrete) presheaf on `c` elements.
pub fn mini_const(n : Int32, c : Int32) -> MiniTy {
  let card : Array[Int32] = []
  for _ in 0..<@cubical.pow3(n) {
    card.push(c)
  }
  mini_build(n, card, fn(_big, _face) { @cubical.fn_id(c) })
}

///|
/// The Boolean line whose generic fibre is swapped at the `1`-face
/// (a miniature of `ua(not)`): restrictions from the generic stage
/// are the identity to the `0`-face and the swap to the `1`-face.
pub fn mini_swap_line() -> MiniTy {
  let card : Array[Int32] = []
  for _ in 0..<@cubical.pow3(1) {
    card.push(2)
  }
  mini_build(1, card, fn(big, face) {
    if big == face {
      @cubical.fn_id(2)
    } else if big == 2 && face == 1 {
      [1, 0]
    } else {
      @cubical.fn_id(2)
    }
  })
}

///|
/// Constant extension along a fresh (last) dimension.
fn mini_extend(x : MiniTy) -> MiniTy {
  let old = @cubical.pow3(x.n)
  let card : Array[Int32] = []
  for s in 0..<@cubical.pow3(x.n + 1) {
    card.push(x.card[s % old])
  }
  mini_build(x.n + 1, card, fn(big, face) {
    x.mini_res_fn(big % old, face % old)
  })
}

///|
/// The path type `Path_x a b`, computed exactly as in the cubical
/// layer: its elements at stage `sigma` are the cubes of the
/// extended type over `sigma x I` whose two end faces are `a` and
/// `b` restricted to `sigma`.
pub fn mini_path_ty(x : MiniTy, a : Int32, b : Int32) -> MiniTy {
  let y = mini_extend(x)
  let base = @cubical.pow3(x.n)
  let gen = @cubical.generic_cube(x.n)
  let elems : Array[Array[Int32]] = []
  let card : Array[Int32] = []
  for s in 0..<base {
    let mid = s + 2 * base
    let sa = x.mini_restrict(gen, s, a)
    let sb = x.mini_restrict(gen, s, b)
    let list : Array[Int32] = []
    for z in 0..<y.card[mid] {
      if y.mini_restrict(mid, s, z) == sa &&
        y.mini_restrict(mid, s + base, z) == sb {
        list.push(z)
      }
    }
    card.push(list.length())
    elems.push(list)
  }
  mini_build(x.n, card, fn(big, face) {
    let out : Array[Int32] = []
    for z in elems[big] {
      let w = y.mini_restrict(big + 2 * base, face + 2 * base, z)
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
/// Is the stage-wise subset (bitmasks over elements at each stage)
/// a subobject, i.e. stable under every restriction?
pub fn mini_is_subobject(x : MiniTy, subset : Array[Int32]) -> Bool {
  let total = @cubical.pow3(x.n)
  for big in 0..<total {
    for face in 0..<total {
      if @cubical.is_subface(face, big, x.n) {
        for e in 0..<x.card[big] {
          if ((subset[big] >> e) & 1) == 1 {
            let r = x.mini_restrict(big, face, e)
            if ((subset[face] >> r) & 1) == 0 {
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
/// Decide local complementedness: both the subset and its
/// stage-wise complement must be subobjects.  This is a finite
/// decision -- all stage-wise data is enumerated.
pub fn mini_is_complemented(x : MiniTy, subset : Array[Int32]) -> Bool {
  let total = @cubical.pow3(x.n)
  let full : Array[Int32] = []
  for s in 0..<total {
    full.push((1 << x.card[s]) - 1)
  }
  let complement : Array[Int32] = []
  for s in 0..<total {
    complement.push(full[s] ^ subset[s])
  }
  mini_is_subobject(x, subset) && mini_is_subobject(x, complement)
}

///|
/// The number of complemented stage-wise subsets of `x`, by
/// exhaustive enumeration (kept small: cards and stages are tiny).
pub fn complemented_subobject_count_for(x : MiniTy) -> Int32 {
  let total = @cubical.pow3(x.n)
  // Encode a stage-wise subset by one mask per stage; enumerate the
  // product of the per-stage mask ranges.
  let ranges : Array[Int32] = []
  for s in 0..<total {
    ranges.push(1 << x.card[s])
  }
  let mut combos = 1
  for r in ranges {
    combos = combos * r
  }
  let mut count = 0
  for code in 0..<combos {
    let subset : Array[Int32] = []
    let mut rest = code
    for s in 0..<total {
      subset.push(rest % ranges[s])
      rest = rest / ranges[s]
    }
    if mini_is_complemented(x, subset) {
      count = count + 1
    }
  }
  count
}

///|
pub fn complemented_subobject_count() -> Int32 {
  complemented_subobject_count_for(mini_const(1, 2))
}

///|
pub fn check_path_locally_complemented() -> Bool {
  // Miniature model is a presheaf, and cross-checks against the
  // cubical layer's path types.
  let x = mini_const(1, 2)
  if !x.mini_check() || !mini_swap_line().mini_check() {
    return false
  }
  let p00 = mini_path_ty(x, 0, 0)
  let p01 = mini_path_ty(x, 0, 1)
  if !p00.mini_check() || !p01.mini_check() {
    return false
  }
  let gen = @cubical.generic_cube(1)
  if p00.card[gen] != 1 || p01.card[gen] != 0 {
    return false
  }
  // Bridge to `@cubical`: the same path types computed there.
  let cx = @cubical.const_ty(1, 2)
  if @cubical.path_ty(cx, 0, 0).generic_card() != 1 ||
    @cubical.path_ty(cx, 0, 1).generic_card() != 0 {
    return false
  }
  let not_iso = @cubical.Iso::new(2, 2, [1, 0], [1, 0])
  let ual = @cubical.ua(not_iso)
  if @cubical.path_ty(ual, 0, 0).generic_card() !=
    mini_path_ty(mini_swap_line(), 0, 0).card[gen] {
    return false
  }
  // Complementedness decisions on path types (stages of the
  // 1-cube are codes 0, 1, and the generic code 2).
  let stages = @cubical.pow3(1)
  let empty : Array[Int32] = []
  let full : Array[Int32] = []
  let generic_only : Array[Int32] = []
  for s in 0..<stages {
    empty.push(0)
    full.push((1 << p00.card[s]) - 1)
    generic_only.push(if s == gen { 1 } else { 0 })
  }
  if !mini_is_complemented(p00, empty) || !mini_is_complemented(p00, full) {
    return false
  }
  // A subset present only at the generic stage is not even a
  // subobject (its elements restrict to the faces), so it is
  // decided *not* locally complemented.
  if mini_is_subobject(p00, generic_only) ||
    mini_is_complemented(p00, generic_only) {
    return false
  }
  // For the constant type, restriction maps are identities, so a
  // stage-wise subset is complemented iff it is given by one fixed
  // subset of elements at every stage: of the `4^3` stage-wise
  // subsets of `mini_const(1, 2)` exactly `4` are complemented
  // (the empty set, the two singletons, and the full set, each
  // chosen uniformly over all stages).
  if complemented_subobject_count() != 4 {
    return false
  }
  // For the path presheaf `p00` (a singleton at every stage with
  // identity restrictions) the complemented subsets are exactly
  // the empty and the full one.
  complemented_subobject_count_for(p00) == 2
}
