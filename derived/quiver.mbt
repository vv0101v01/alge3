///|
/// An arrow `i -> j` of a finite quiver together with a matrix
/// `mat[t][s] : V_i -> V_j` (rows indexed by the target basis).
pub struct QArrow {
  src : Int32
  tgt : Int32
  mat : Array[Array[Int32]]
}

///|
pub struct QRep {
  nverts : Int32
  dims : Array[Int32]
  arrows : Array[QArrow]
}

///|
pub fn QRep::new(
  nverts : Int32,
  dims : Array[Int32],
  arrows : Array[QArrow],
) -> QRep {
  QRep::{ nverts, dims, arrows, }
}

///|
fn zeros_matrix(rows : Int32, cols : Int32) -> Array[Array[Int32]] {
  let m : Array[Array[Int32]] = []
  for _ in 0..<rows {
    let r : Array[Int32] = []
    for _ in 0..<cols {
      r.push(0)
    }
    m.push(r)
  }
  m
}

///|
/// Tangent space of the representation stack at a representation:
///
/// `C^0 = ⊕_v End(V_v)`, `C^1 = ⊕_{a: i->j} Hom(V_i,V_j)`,
/// `δ^0(X)_a = X_{t(a)} A_a - A_a X_{s(a)}`.
///
/// Returns `(dim Ext^0, dim Ext^1)`.  `Ext^0` is the Lie algebra of the
/// stabiliser of the representation, and `Ext^1` is the Zariski tangent
/// space of the formal moduli space `Rep(Q,d)//GL(d)`.
pub fn QRep::ext01(self : QRep) -> (Int32, Int32) {
  let c0_off : Array[Int32] = []
  let mut acc = 0
  for i in 0..<self.nverts {
    c0_off.push(acc)
    acc = acc + self.dims[i] * self.dims[i]
  }
  let c0dim = acc
  let c1_off : Array[Int32] = []
  acc = 0
  for a in 0..<self.arrows.length() {
    c1_off.push(acc)
    acc = acc + self.dims[self.arrows[a].tgt] * self.dims[self.arrows[a].src]
  }
  let c1dim = acc
  let d0 = zeros_matrix(c1dim, c0dim)
  for a in 0..<self.arrows.length() {
    let ar = self.arrows[a]
    let di = self.dims[ar.src]
    let dj = self.dims[ar.tgt]
    // X_tgt * A
    for p in 0..<dj {
      for l in 0..<dj {
        for q in 0..<di {
          let row = c1_off[a] + p * di + q
          let col = c0_off[ar.tgt] + p * dj + l
          d0[row][col] = fp_norm(d0[row][col] + ar.mat[l][q], 1009)
        }
      }
    }
    // - A * X_src
    for p in 0..<dj {
      for l in 0..<di {
        for q in 0..<di {
          let row = c1_off[a] + p * di + q
          let col = c0_off[ar.src] + l * di + q
          d0[row][col] = fp_norm(d0[row][col] - ar.mat[p][l], 1009)
        }
      }
    }
  }
  let r0 = fp_rank(d0, 1009)
  (c0dim - r0, c1dim - r0)
}

///|
pub fn arrow(src : Int32, tgt : Int32, mat : Array[Array[Int32]]) -> QArrow {
  QArrow::{ src, tgt, mat, }
}
