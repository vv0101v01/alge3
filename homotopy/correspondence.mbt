///|
/// A span / correspondence `A <- R -> B`, represented by the relation matrix
/// `rel : A x B -> {0,1}`.  Composition of spans is pullback followed by
/// projection, which on relation matrices is Boolean matrix multiplication
/// (`OR` of `AND`s).  For profunctors between discrete categories this is
/// exactly composition of profunctors; for `∞`-categories the same formula
/// computes the correspondence composition up to coherent homotopy.
pub struct Span {
  left : Int32
  right : Int32
  rel : BoolMat
}

///|
pub fn Span::new(left : Int32, right : Int32, rel : BoolMat) -> Span {
  Span::{ left, right, rel, }
}

///|
pub fn Span::identity(n : Int32) -> Span {
  Span::{ left: n, right: n, rel: BoolMat::identity(n), }
}

///|
pub fn Span::compose(self : Span, other : Span) -> Span {
  // self : A -> B, other : B -> C
  Span::{
    left: self.left,
    right: other.right,
    rel: self.rel.mul_or(other.rel),
  }
}

///|
pub fn Span::opposite(self : Span) -> Span {
  Span::{ left: self.right, right: self.left, rel: self.rel.transpose(), }
}

///|
/// Explicit pullback construction for finite spans, used to verify that
/// Boolean matrix multiplication really computes span composition.
/// Returns the composed relation as a matrix.
pub fn pullback_compose(
  a : Int32,
  b : Int32,
  c : Int32,
  f : Array[Int32], // X -> A
  g : Array[Int32], // X -> B
  h : Array[Int32], // Y -> B
  k : Array[Int32], // Y -> C
) -> BoolMat {
  let rows : Array[Bits] = []
  for _ in 0..<a {
    rows.push(Bits::new(c))
  }
  for x in 0..<f.length() {
    for y in 0..<h.length() {
      if g[x] == h[y] {
        rows[f[x]].set(k[y])
      }
    }
  }
  let _ = b
  BoolMat::new(rows, c)
}

///|
/// Relation matrix from a pair of maps out of a common finite set.
pub fn span_of_maps(
  a : Int32,
  b : Int32,
  f : Array[Int32],
  g : Array[Int32],
) -> Span {
  let rows : Array[Bits] = []
  for _ in 0..<a {
    rows.push(Bits::new(b))
  }
  for x in 0..<f.length() {
    rows[f[x]].set(g[x])
  }
  Span::{ left: a, right: b, rel: BoolMat::new(rows, b), }
}
