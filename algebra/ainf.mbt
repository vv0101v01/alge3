///|
using @core {type Bits, type ChainComplex}

///|
/// A finite graded `F_2`-vector space with degrees 0, 1, ..., D.
pub struct GradedSpace {
  dims : Array[Int32]
  offsets : Array[Int32]
  total : Int32
}

///|
pub fn GradedSpace::new(dims : Array[Int32]) -> GradedSpace {
  let offsets : Array[Int32] = []
  let mut acc = 0
  for d in dims {
    offsets.push(acc)
    acc = acc + d
  }
  GradedSpace::{ dims, offsets, total: acc, }
}

///|
pub fn GradedSpace::degree(self : GradedSpace, i : Int32) -> Int32 {
  let mut ans = -1
  for d in 0..<self.dims.length() {
    if i >= self.offsets[d] && i < self.offsets[d] + self.dims[d] {
      ans = d
    }
  }
  ans
}

///|
fn zeros1(n : Int32) -> Array[Bits] {
  let a : Array[Bits] = []
  for _ in 0..<n {
    a.push(Bits::new(n))
  }
  a
}

///|
fn zeros2(n : Int32) -> Array[Array[Bits]] {
  let a : Array[Array[Bits]] = []
  for _ in 0..<n {
    a.push(zeros1(n))
  }
  a
}

///|
fn zeros3(n : Int32) -> Array[Array[Array[Bits]]] {
  let a : Array[Array[Array[Bits]]] = []
  for _ in 0..<n {
    a.push(zeros2(n))
  }
  a
}

///|
/// An `A_∞`-algebra structure on a finite graded space over `F_2`, truncated
/// at `m_3`.  The operations have degrees `|m_1| = 1`, `|m_2| = 0`,
/// `|m_3| = -1`; the Stasheff identities checked below are
///
/// `m_1 m_1 = 0`
/// `m_1 m_2 + m_2 (m_1 ⊗ 1 + 1 ⊗ m_1) = 0`
/// `m_1 m_3 + m_3 (m_2 ⊗ 1 + 1 ⊗ m_2) + m_2 (m_1 ⊗ 1 ⊗ 1 + 1 ⊗ m_1 ⊗ 1 + 1 ⊗ 1 ⊗ m_1) = 0`.
pub struct AInf {
  space : GradedSpace
  m1 : Array[Bits]
  m2 : Array[Array[Bits]]
  m3 : Array[Array[Array[Bits]]]
}

///|
pub fn AInf::zero(space : GradedSpace) -> AInf {
  AInf::{
    space,
    m1: zeros1(space.total),
    m2: zeros2(space.total),
    m3: zeros3(space.total),
  }
}

///|
/// Add `to` to `m_1(from)` (XOR, i.e. addition in `F_2`).
pub fn AInf::set_m1(self : AInf, from : Int32, to_ : Int32) -> Unit {
  self.m1[from].flip(to_)
}

///|
pub fn AInf::set_m2(self : AInf, i : Int32, j : Int32, to_ : Int32) -> Unit {
  self.m2[i][j].flip(to_)
}

///|
pub fn AInf::set_m3(
  self : AInf,
  i : Int32,
  j : Int32,
  k : Int32,
  to_ : Int32,
) -> Unit {
  self.m3[i][j][k].flip(to_)
}

///|
fn single(i : Int32, n : Int32) -> Bits {
  let b = Bits::new(n)
  b.set(i)
  b
}

///|
fn apply1(m1 : Array[Bits], v : Bits) -> Bits {
  let acc = Bits::new(m1.length())
  let x = v.copy()
  while true {
    match x.first_set() {
      None => break
      Some(i) => {
        acc.xor_inplace(m1[i])
        x.clear_bit(i)
      }
    }
  }
  acc
}

///|
fn apply2(m2 : Array[Array[Bits]], a : Bits, b : Bits) -> Bits {
  let acc = Bits::new(m2.length())
  let x = a.copy()
  while true {
    match x.first_set() {
      None => break
      Some(i) => {
        let y = b.copy()
        while true {
          match y.first_set() {
            None => break
            Some(j) => {
              acc.xor_inplace(m2[i][j])
              y.clear_bit(j)
            }
          }
        }
        x.clear_bit(i)
      }
    }
  }
  acc
}

///|
fn apply3(m3 : Array[Array[Array[Bits]]], a : Bits, b : Bits, c : Bits) -> Bits {
  let acc = Bits::new(m3.length())
  let x = a.copy()
  while true {
    match x.first_set() {
      None => break
      Some(i) => {
        let y = b.copy()
        while true {
          match y.first_set() {
            None => break
            Some(j) => {
              let z = c.copy()
              while true {
                match z.first_set() {
                  None => break
                  Some(k) => {
                    acc.xor_inplace(m3[i][j][k])
                    z.clear_bit(k)
                  }
                }
              }
              y.clear_bit(j)
            }
          }
        }
        x.clear_bit(i)
      }
    }
  }
  acc
}

///|
/// `m_1^2 = 0`.
pub fn AInf::check_m1sq(self : AInf) -> Bool {
  let mut ok = true
  for i in 0..<self.space.total {
    if !apply1(self.m1, self.m1[i]).is_zero() {
      ok = false
    }
  }
  ok
}

///|
/// Degree compatibility of the three operations.
pub fn AInf::check_degrees(self : AInf) -> Bool {
  let sp = self.space
  let mut ok = true
  for i in 0..<sp.total {
    let di = sp.degree(i)
    let x = self.m1[i].copy()
    while true {
      match x.first_set() {
        None => break
        Some(j) => {
          if sp.degree(j) != di + 1 {
            ok = false
          }
          x.clear_bit(j)
        }
      }
    }
    for j in 0..<sp.total {
      let y = self.m2[i][j].copy()
      while true {
        match y.first_set() {
          None => break
          Some(k) => {
            if sp.degree(k) != di + sp.degree(j) {
              ok = false
            }
            y.clear_bit(k)
          }
        }
      }
      for k in 0..<sp.total {
        let z = self.m3[i][j][k].copy()
        while true {
          match z.first_set() {
            None => break
            Some(l) => {
              if sp.degree(l) != di + sp.degree(j) + sp.degree(k) - 1 {
                ok = false
              }
              z.clear_bit(l)
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// The derivation identity for `m_2` with respect to `m_1`.
pub fn AInf::check_derivation(self : AInf) -> Bool {
  let n = self.space.total
  let mut ok = true
  for i in 0..<n {
    for j in 0..<n {
      let acc = apply1(self.m1, self.m2[i][j])
      acc.xor_inplace(apply2(self.m2, self.m1[i], single(j, n)))
      acc.xor_inplace(apply2(self.m2, single(i, n), self.m1[j]))
      if !acc.is_zero() {
        ok = false
      }
    }
  }
  ok
}

///|
/// The Stasheff identity for three inputs.
pub fn AInf::check_stasheff3(self : AInf) -> Bool {
  let n = self.space.total
  let mut ok = true
  for i in 0..<n {
    for j in 0..<n {
      for k in 0..<n {
        let acc = apply1(self.m1, self.m3[i][j][k])
        acc.xor_inplace(apply3(self.m3, self.m1[i], single(j, n), single(k, n)))
        acc.xor_inplace(apply3(self.m3, single(i, n), self.m1[j], single(k, n)))
        acc.xor_inplace(apply3(self.m3, single(i, n), single(j, n), self.m1[k]))
        acc.xor_inplace(apply2(self.m2, self.m2[i][j], single(k, n)))
        acc.xor_inplace(apply2(self.m2, single(i, n), self.m2[j][k]))
        if !acc.is_zero() {
          ok = false
        }
      }
    }
  }
  ok
}

///|
pub fn AInf::check_all(self : AInf) -> Bool {
  self.check_m1sq() &&
  self.check_degrees() &&
  self.check_derivation() &&
  self.check_stasheff3()
}

///|
/// Exterior algebra `Λ(e_1,e_2)` over `F_2`: basis `1, e_1, e_2, e_1e_2`,
/// `m_1 = 0`, `m_3 = 0`.
pub fn exterior_algebra() -> AInf {
  let a = AInf::zero(GradedSpace::new([1, 2, 1]))
  // unit (set the (0,0) entry exactly once: `set_m2` is XOR)
  a.set_m2(0, 0, 0)
  for j in 1..<4 {
    a.set_m2(0, j, j)
    a.set_m2(j, 0, j)
  }
  a.set_m2(1, 2, 3)
  a.set_m2(2, 1, 3)
  a
}

///|
/// The dga `F_2[1,x]` with `|x| = 0`, `|y| = 1`, `d(x) = y`, `d(y) = 0`,
/// `x^2 = 0`, all products with `y` equal to zero.
pub fn line_dga() -> AInf {
  let a = AInf::zero(GradedSpace::new([2, 1]))
  // 0 = 1, 1 = x, 2 = y
  a.set_m1(1, 2)
  a.set_m2(0, 0, 0)
  for j in 1..<3 {
    a.set_m2(0, j, j)
    a.set_m2(j, 0, j)
  }
  a
}

///|
/// Polynomial algebra `F_2[x]/(x^3)`: `1, x, x^2`.
pub fn truncated_polynomial() -> AInf {
  let a = AInf::zero(GradedSpace::new([1, 1, 1]))
  a.set_m2(0, 0, 0)
  for j in 1..<3 {
    a.set_m2(0, j, j)
    a.set_m2(j, 0, j)
  }
  a.set_m2(1, 1, 2)
  a
}
