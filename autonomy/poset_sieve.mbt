///|
// Finite poset categories and Alexandrov down-closed sieves forming a
// complete bi-Heyting algebra (for cubical presheaf duality verification).

///|
pub struct FinitePosetCat {
  nobj : Int32
  nmor : Int32
  dom : Array[Int32]
  cod : Array[Int32]
  comp : Array[Array[Int32]] // comp[f][g] = f ∘ g (where dom[f] == cod[g]), or -1
}

///|
pub fn cat_poset(nobj : Int32, edges : Array[(Int32, Int32)]) -> FinitePosetCat {
  let reach : Array[Array[Bool]] = []
  for i in 0..<nobj {
    let row = Array::make(nobj, false)
    row[i] = true
    reach.push(row)
  }
  for e in edges {
    let (u, v) = e
    if u >= 0 && u < nobj && v >= 0 && v < nobj {
      reach[u][v] = true
    }
  }
  for k in 0..<nobj {
    for i in 0..<nobj {
      for j in 0..<nobj {
        if reach[i][k] && reach[k][j] {
          reach[i][j] = true
        }
      }
    }
  }
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  let pair_idx : Array[Array[Int32]] = []
  for i in 0..<nobj {
    let row = Array::make(nobj, -1)
    for j in 0..<nobj {
      if reach[i][j] {
        row[j] = dom.length()
        dom.push(i)
        cod.push(j)
      }
    }
    pair_idx.push(row)
  }
  let nmor = dom.length()
  let comp : Array[Array[Int32]] = []
  for f in 0..<nmor {
    let row = Array::make(nmor, -1)
    for g in 0..<nmor {
      if cod[g] == dom[f] {
        row[g] = pair_idx[dom[g]][cod[f]]
      }
    }
    comp.push(row)
  }
  FinitePosetCat::{ nobj, nmor, dom, cod, comp, }
}

///|
pub fn cat_arrow() -> FinitePosetCat {
  cat_poset(2, [(0, 1)])
}

///|
#derive(Eq)
pub struct Sieve {
  obj : Int32
  arrows : Array[Int32]
}

///|
pub extend Sieve with Eq::{not_equal, equal}

///|
fn arr_has(xs : Array[Int32], v : Int32) -> Bool {
  for x in xs {
    if x == v {
      return true
    }
  }
  false
}

///|
fn sieve_make(obj : Int32, arrows : Array[Int32]) -> Sieve {
  let uniq : Array[Int32] = []
  for a in arrows {
    if !arr_has(uniq, a) {
      uniq.push(a)
    }
  }
  let n = uniq.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if uniq[j] < uniq[i] {
        let t = uniq[i]
        uniq[i] = uniq[j]
        uniq[j] = t
      }
    }
  }
  Sieve::{ obj, arrows: uniq, }
}

///|
pub fn sieve_maximal(cat : FinitePosetCat, obj : Int32) -> Sieve {
  let arrows : Array[Int32] = []
  for m in 0..<cat.nmor {
    if cat.cod[m] == obj {
      arrows.push(m)
    }
  }
  sieve_make(obj, arrows)
}

///|
fn is_sieve_closed(
  cat : FinitePosetCat,
  obj : Int32,
  arrows : Array[Int32],
) -> Bool {
  for m in arrows {
    if cat.cod[m] != obj {
      return false
    }
    for g in 0..<cat.nmor {
      if cat.cod[g] == cat.dom[m] {
        let comp_mg = cat.comp[m][g]
        if comp_mg >= 0 && !arr_has(arrows, comp_mg) {
          return false
        }
      }
    }
  }
  true
}

///|
pub fn all_sieves_on(cat : FinitePosetCat, obj : Int32) -> Array[Sieve] {
  let max_s = sieve_maximal(cat, obj).arrows
  let k = max_s.length()
  let lim = 1 << k
  let out : Array[Sieve] = []
  for mask in 0..<lim {
    let cand : Array[Int32] = []
    for i in 0..<k {
      if (mask & (1 << i)) != 0 {
        cand.push(max_s[i])
      }
    }
    if is_sieve_closed(cat, obj, cand) {
      out.push(sieve_make(obj, cand))
    }
  }
  out
}

///|
pub fn sieve_subset(a : Sieve, b : Sieve) -> Bool {
  for x in a.arrows {
    if !arr_has(b.arrows, x) {
      return false
    }
  }
  true
}

///|
pub fn sieve_union(a : Sieve, b : Sieve) -> Sieve {
  let out : Array[Int32] = []
  for x in a.arrows {
    out.push(x)
  }
  for x in b.arrows {
    out.push(x)
  }
  sieve_make(a.obj, out)
}

///|
pub fn sieve_inter(a : Sieve, b : Sieve) -> Sieve {
  let out : Array[Int32] = []
  for x in a.arrows {
    if arr_has(b.arrows, x) {
      out.push(x)
    }
  }
  sieve_make(a.obj, out)
}

///|
fn sieve_heyting_neg(cat : FinitePosetCat, a : Sieve) -> Sieve {
  let max_s = sieve_maximal(cat, a.obj)
  let out : Array[Int32] = []
  for m in max_s.arrows {
    let mut disjoint_below = true
    for g in 0..<cat.nmor {
      if cat.cod[g] == cat.dom[m] {
        let mg = cat.comp[m][g]
        if mg >= 0 && arr_has(a.arrows, mg) {
          disjoint_below = false
          break
        }
      }
    }
    if disjoint_below {
      out.push(m)
    }
  }
  sieve_make(a.obj, out)
}

///|
pub fn sieve_double_negation(cat : FinitePosetCat, a : Sieve) -> Sieve {
  sieve_heyting_neg(cat, sieve_heyting_neg(cat, a))
}

///|
pub fn sieve_coheyting_sub(cat : FinitePosetCat, a : Sieve, b : Sieve) -> Sieve {
  // Smallest sieve containing { f ∈ A | f ∉ B } is its precomposition downward closure.
  let raw_diff : Array[Int32] = []
  for f in a.arrows {
    if !arr_has(b.arrows, f) {
      raw_diff.push(f)
    }
  }
  let closed : Array[Int32] = []
  for f in raw_diff {
    closed.push(f)
    for g in 0..<cat.nmor {
      if cat.cod[g] == cat.dom[f] {
        let fg = cat.comp[f][g]
        if fg >= 0 {
          closed.push(fg)
        }
      }
    }
  }
  sieve_make(a.obj, closed)
}

///|
pub fn sieve_coheyting_neg(cat : FinitePosetCat, a : Sieve) -> Sieve {
  sieve_coheyting_sub(cat, sieve_maximal(cat, a.obj), a)
}

///|
pub fn sieve_coheyting_boundary(cat : FinitePosetCat, a : Sieve) -> Sieve {
  sieve_inter(a, sieve_coheyting_neg(cat, a))
}
