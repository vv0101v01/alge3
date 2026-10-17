///|
fn perm_rec(
  n : Int32,
  cur : Array[Int32],
  used : Array[Bool],
  out : Array[Array[Int32]],
) -> Unit {
  if cur.length() == n {
    let cp : Array[Int32] = []
    for v in cur {
      cp.push(v)
    }
    out.push(cp)
  } else {
    for v in 0..<n {
      if !used[v] {
        let cur2 : Array[Int32] = []
        for w in cur {
          cur2.push(w)
        }
        cur2.push(v)
        let used2 : Array[Bool] = []
        for u in used {
          used2.push(u)
        }
        used2[v] = true
        perm_rec(n, cur2, used2, out)
      }
    }
  }
}

///|
/// All permutations of `Fin n` (there are `n!`), for exhaustive finite
/// verification of the univalence computation rules.
pub fn all_permutations(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  perm_rec(n, [], Array::make(n, false), out)
  out
}

///|
/// An equivalence of finite sets from a permutation, if it is one.
pub fn perm_iso(f : Array[Int32]) -> Iso? {
  iso_of_fn(f, f.length(), f.length())
}

///|
/// The construction at the heart of cubical univalence.  For an
/// equivalence `e : A ≃ B` of finite types,
///
/// ```text
/// ua(e) : Path U A B
/// ua(e)(i) = Glue B [ (i=0) ↦ (A, e), (i=1) ↦ (B, id) ]
/// ```
///
/// The two endpoints hold *strictly* (face restriction of a Glue type on
/// its cofibration is the glued type itself), which is exactly what the
/// old univalence axiom could not arrange computationally.
pub fn ua(e : Iso) -> CubeTy {
  // The partial type: A at i=0, B at i=1 (the value at the generic stage
  // is irrelevant; we use A with restriction e to i=1).
  let card : Array[Int32] = [e.dom, e.cod, e.dom]
  let t = build_ty(1, card, fn(big, face) {
    if big == 2 && face == 0 {
      fn_id(e.dom)
    } else if big == 2 && face == 1 {
      e.fwd
    } else {
      fn_id(card[big])
    }
  })
  let base = const_ty(1, e.cod)
  let efam : Array[Array[Int32]] = [e.fwd, fn_id(e.cod), []]
  let phi = COr(face_cof(0, 0), face_cof(0, 1))
  glue_ty(phi, t, base, efam)
}

///|
/// The constant path `refl : Path U A A` in the finite universe.
pub fn refl_line(c : Int32) -> CubeTy {
  const_ty(1, c)
}

///|
/// Path symmetry in the universe: reverse the line.
pub fn sym_line(p : CubeTy) -> CubeTy {
  reverse_ty(p, 0)
}

///|
/// `idtoeqv : (A =_U B) -> A ≃ B`, defined by transport along the line:
/// the forward map sends `a` to `comp^i p [] a`, the backward map is
/// transport along the reversed line.  Here it is read off composition:
/// the transport isomorphism of the line `p`.
pub fn idtoeqv(p : CubeTy) -> Iso? {
  stage_line_iso(p, generic_cube(1), 0)
}

///|
/// Transport along a path in the finite universe: `transp^i (p i) ⊥ a`.
pub fn transport_path(p : CubeTy, a : Int32) -> Int32? {
  transp_line(p, 0, a)
}

///|
/// The computational content of univalence, checked exhaustively:
/// `transport (ua e) a = e a` for every `a`.  In the axiom-based theory
/// this is the propositional `uaβ`; here it is the *output* of `comp` in
/// a Glue type, hence a decidable equality of programs.
pub fn check_ua_beta(e : Iso) -> Bool {
  if !e.check() {
    return false
  }
  let p = ua(e)
  let mut ok = true
  for a in 0..<e.dom {
    match transport_path(p, a) {
      Some(v) => if v != e.fwd[a] { ok = false }
      None => ok = false
    }
  }
  ok
}

///|
/// The other round trip: every line of finite types `p` (with bijective
/// restrictions) is stage-wise isomorphic, naturally, to
/// `ua(idtoeqv p)`.  The isomorphism is the identity at the endpoints and
/// `res(p, generic → 1)` at the generic stage; naturality at the `0` face
/// is the identity `e^{-1} ∘ res_1 = res_0` for `e = res_1 ∘ res_0^{-1}`.
/// Together with `check_ua_beta` this verifies that `ua` is an equivalence
/// `(A ≃ B) ≃ (A =_U B)` in the finite model.
pub fn check_ua_eta(p : CubeTy) -> Bool {
  match idtoeqv(p) {
    None => false
    Some(e) => {
      let q = ua(e)
      let r1 = p.res_fn(2, 1)
      match fn_inv(r1, p.card[1]) {
        None => false
        Some(r1_inv) => {
          let iso = TyIso::{
            fwd: [fn_id(p.card[0]), fn_id(p.card[1]), r1],
            bwd: [fn_id(p.card[0]), fn_id(p.card[1]), r1_inv],
          }
          check_ty_iso(p, q, iso)
        }
      }
    }
  }
}

///|
/// Composition in the universe.  Given types `A` and `E` over
/// `Ψ × I` (composition direction `dir`, required to be the *last*
/// coordinate), a cofibration `phi` over `Ψ`, and stage-wise equivalences
/// `efam[σ] : E(σ) ≃ A(σ)` on the extent of `phi` (lifted constantly along
/// `dir`), produce the type over `Ψ`
///
/// ```text
/// comp^dir U [phi ↦ (E, efam)] A
///   = Glue [phi ↦ (E(1), e')] A(1),
///   e' = transp^A ∘ efam(0) ∘ (transp^E)^{-1}
/// ```
///
/// where the transports are taken stage-wise in `Ψ`.  This is the CCHM
/// formula: composition in `U` *is* a Glue type, and the composed
/// equivalence is the conjugation of the tube equivalence by the two
/// transports.
pub fn comp_universe(
  a : CubeTy,
  e_ty : CubeTy,
  phi : Cof,
  efam : Array[Array[Int32]],
  dir : Int32,
) -> CubeTy? {
  let m = a.n - 1
  let base = pow3(m)
  let a1 = face_ty(a, dir, 1)
  let e1 = face_ty(e_ty, dir, 1)
  let efam2 : Array[Array[Int32]] = []
  for s in 0..<pow3(m) {
    if phi.holds_code(s, m) {
      let mid = s + 2 * base
      let ta = stage_line_iso(a, mid, dir)
      let te = stage_line_iso(e_ty, mid, dir)
      match (ta, te) {
        (Some(ta), Some(te)) => {
          let f : Array[Int32] = []
          for u in 0..<e1.card[s] {
            f.push(ta.fwd[efam[s][te.bwd[u]]])
          }
          efam2.push(f)
        }
        _ => return None
      }
    } else {
      efam2.push([])
    }
  }
  Some(glue_ty(phi, e1, a1, efam2))
}

///|
/// Composition (transitivity) of paths in the finite universe, built from
/// `comp` in `U`.  For lines `p : A ⇝ B` and `q : B ⇝ C` over dimension
/// `x`, form the square over `(x, j)` whose total type is `p` constant in
/// `j`, with tube `q(j)` glued on the face `x = 1` via the equivalences
/// `id_B`, `res(q)`, `(transp q)^{-1}` at `j = 0, *, 1`; then
/// `comp^j U` returns a line `A ⇝ C` whose transport is
/// `transp(q) ∘ transp(p)`.
pub fn comp_path_universe(p : CubeTy, q : CubeTy) -> CubeTy? {
  let a_sq = extend_ty(p)
  let e_sq = swap_dims_ty(extend_ty(q), 0, 1)
  let bcard = p.card[1]
  match idtoeqv(q) {
    None => None
    Some(tq) => {
      let efam : Array[Array[Int32]] = []
      for code in 0..<9 {
        let xd = subcube_digit(code, 0)
        let jd = subcube_digit(code, 1)
        if xd == 1 {
          if jd == 0 {
            efam.push(fn_id(bcard))
          } else if jd == 1 {
            efam.push(tq.bwd)
          } else {
            efam.push(q.res_fn(2, 0))
          }
        } else {
          efam.push([])
        }
      }
      comp_universe(a_sq, e_sq, face_cof(0, 1), efam, 1)
    }
  }
}
