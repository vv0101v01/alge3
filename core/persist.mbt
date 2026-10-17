///|
/// One cell of a filtered complex.  `boundary` contains indices of cells that
/// must occur earlier in the filtration (faces are born no later than cells).
pub struct FilteredCell {
  dim : Int32
  birth : Int32
  boundary : Array[Int32]
}

///|
pub fn FilteredCell::new(
  dim : Int32,
  birth : Int32,
  boundary : Array[Int32],
) -> FilteredCell {
  FilteredCell::{ dim, birth, boundary, }
}

///|
pub struct Filtration {
  cells : Array[FilteredCell]
}

///|
pub struct PersistencePair {
  dim : Int32
  birth : Int32
  death : Int32?
}

///|
pub fn Filtration::new(cells : Array[FilteredCell]) -> Filtration {
  Filtration::{ cells, }
}

///|
/// Standard column reduction for persistent homology.  Columns are processed
/// in filtration order; a nonzero reduced column with lowest pivot `p` pairs
/// the positive cell `p` with the current negative cell `j`.  Positive cells
/// that never appear as a pivot are essential classes.
///
/// Complexity: `O(m^3 / 64)` word operations for `m` cells, compared with
/// `O(m^3)` for a scalar implementation.
pub fn Filtration::persistence(self : Filtration) -> Array[PersistencePair] {
  let m = self.cells.length()
  let reduced : Array[Bits] = []
  let low : Array[Int32] = []
  let positive : Array[Bool] = []
  let paired : Array[Bool] = []
  for _ in 0..<m {
    reduced.push(Bits::new(m))
    low.push(-1)
    positive.push(false)
    paired.push(false)
  }
  let pairs : Array[PersistencePair] = []
  for j in 0..<m {
    let col = Bits::new(m)
    for f in self.cells[j].boundary {
      col.set(f)
    }
    let mut v = col
    let mut nonzero = false
    while !v.is_zero() {
      match v.first_set() {
        None => break
        Some(p) =>
          if low[p] < 0 {
            low[p] = j
            reduced[j] = v
            nonzero = true
            paired[p] = true
            pairs.push(PersistencePair::{
              dim: self.cells[p].dim,
              birth: self.cells[p].birth,
              death: Some(self.cells[j].birth),
            })
            v = Bits::new(m)
          } else {
            v = v.xor(reduced[low[p]])
          }
      }
    }
    if !nonzero {
      positive[j] = true
    }
  }
  for j in 0..<m {
    if positive[j] && !paired[j] {
      pairs.push(PersistencePair::{
        dim: self.cells[j].dim,
        birth: self.cells[j].birth,
        death: None,
      })
    }
  }
  pairs
}

///|
/// Betti number at filtration value `t`: number of pairs alive at `t`
/// (birth <= t and (death is None or death > t)).
pub fn Filtration::betti_at(self : Filtration, t : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<8 {
    out.push(0)
  }
  for p in self.persistence() {
    if p.birth <= t {
      let alive = match p.death {
        None => true
        Some(d) => d > t
      }
      if alive {
        out[p.dim] = out[p.dim] + 1
      }
    }
  }
  out
}

///|
/// Persistence diagram as human-readable lines.
pub fn Filtration::diagram(self : Filtration) -> String {
  let sb = StringBuilder()
  for p in self.persistence() {
    sb.write_string("dim ")
    sb.write_string(p.dim.to_string())
    sb.write_string(": ")
    sb.write_string(p.birth.to_string())
    sb.write_string(" -> ")
    match p.death {
      None => sb.write_string("inf")
      Some(d) => sb.write_string(d.to_string())
    }
    sb.write_string("\n")
  }
  sb.to_string()
}
