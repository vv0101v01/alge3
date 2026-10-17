///|
/// A fixed-width bit vector over GF(2). Bit `i` lives in word `i / 64`
/// at position `i % 64` (little-endian words).  All linear algebra in this
/// package is bit-parallel: one machine word XOR handles 64 field elements.
pub struct Bits {
  words : Array[UInt64]
  n : Int32
}

///|
#inline
pub fn popcount64(x : UInt64) -> Int32 {
  let mut y = x
  let mut c = 0
  while y != 0UL {
    y = y & (y - 1UL)
    c = c + 1
  }
  c
}

///|
#inline
pub fn trailing_zeros64(x : UInt64) -> Int32 {
  let mut y = x
  let mut c = 0
  while (y & 1UL) == 0UL && c < 64 {
    y = y >> 1
    c = c + 1
  }
  c
}

///|
pub fn Bits::new(n : Int32) -> Bits {
  Bits::{ words: Array::make((n + 63) / 64, 0UL), n, }
}

///|
pub fn Bits::length(self : Bits) -> Int32 {
  self.n
}

///|
pub fn Bits::copy(self : Bits) -> Bits {
  let ws : Array[UInt64] = []
  for i in 0..<self.words.length() {
    ws.push(self.words[i])
  }
  Bits::{ words: ws, n: self.n, }
}

///|
#inline
pub fn Bits::get(self : Bits, i : Int32) -> Bool {
  ((self.words[i / 64] >> (i % 64)) & 1UL) == 1UL
}

///|
#inline
pub fn Bits::set(self : Bits, i : Int32) -> Unit {
  self.words[i / 64] = self.words[i / 64] | (1UL << (i % 64))
}

///|
/// Toggle bit `i` (addition in `F_2`).
pub fn Bits::flip(self : Bits, i : Int32) -> Unit {
  self.words[i / 64] = self.words[i / 64] ^ (1UL << (i % 64))
}

///|
pub fn Bits::clear_bit(self : Bits, i : Int32) -> Unit {
  self.words[i / 64] = self.words[i / 64] &
    (0xFFFFFFFFFFFFFFFFUL ^ (1UL << (i % 64)))
}

///|
pub fn Bits::is_zero(self : Bits) -> Bool {
  let mut z = true
  for w in self.words {
    if w != 0UL {
      z = false
    }
  }
  z
}

///|
pub fn Bits::weight(self : Bits) -> Int32 {
  let mut s = 0
  for w in self.words {
    s = s + popcount64(w)
  }
  s
}

///|
/// Lowest set bit, or `None` for the zero vector.  This is the pivot rule
/// used by the online Gaussian elimination below.
pub fn Bits::first_set(self : Bits) -> Int32? {
  for i in 0..<self.words.length() {
    if self.words[i] != 0UL {
      return Some(i * 64 + trailing_zeros64(self.words[i]))
    }
  }
  None
}

///|
pub fn Bits::xor(self : Bits, other : Bits) -> Bits {
  let ws : Array[UInt64] = []
  for i in 0..<self.words.length() {
    ws.push(self.words[i] ^ other.words[i])
  }
  Bits::{ words: ws, n: self.n, }
}

///|
pub fn Bits::xor_inplace(self : Bits, other : Bits) -> Unit {
  for i in 0..<self.words.length() {
    self.words[i] = self.words[i] ^ other.words[i]
  }
}

///|
pub fn Bits::or_inplace(self : Bits, other : Bits) -> Unit {
  for i in 0..<self.words.length() {
    self.words[i] = self.words[i] | other.words[i]
  }
}

///|
pub fn Bits::same(self : Bits, other : Bits) -> Bool {
  let mut ok = true
  for i in 0..<self.words.length() {
    if self.words[i] != other.words[i] {
      ok = false
    }
  }
  ok
}
