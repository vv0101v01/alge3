///|
test "rank of small matrices" {
  let zero = BoolMat::zero(3, 4)
  assert_eq(rank_mat(zero), 0)
  let id = BoolMat::identity(4)
  assert_eq(rank_mat(id), 4)
  let rows : Array[Bits] = []
  let r0 = Bits::new(2)
  r0.set(0)
  r0.set(1)
  rows.push(r0)
  let r1 = Bits::new(2)
  r1.set(0)
  r1.set(1)
  rows.push(r1)
  assert_eq(rank_mat(BoolMat::new(rows, 2)), 1)
}

///|
test "matrix multiplication agrees with scalar reference" {
  let a_rows : Array[Bits] = []
  let a0 = Bits::new(3)
  a0.set(0)
  a0.set(2)
  a_rows.push(a0)
  let a1 = Bits::new(3)
  a1.set(1)
  a_rows.push(a1)
  let a = BoolMat::new(a_rows, 3)
  let b_rows : Array[Bits] = []
  let b0 = Bits::new(4)
  b0.set(0)
  b0.set(3)
  b_rows.push(b0)
  let b1 = Bits::new(4)
  b1.set(1)
  b_rows.push(b1)
  let b2 = Bits::new(4)
  b2.set(0)
  b2.set(1)
  b2.set(2)
  b_rows.push(b2)
  let bm = BoolMat::new(b_rows, 4)
  let c = a.mul(bm)
  let d = mul_scalar_reference(a, bm)
  for i in 0..<2 {
    for j in 0..<4 {
      assert_eq(c.get(i, j), d.get(i, j))
    }
  }
}

///|
test "circle homology" {
  // 3 vertices, 3 edges 01,12,20.
  let b1 : Array[Bits] = []
  let e01 = Bits::new(3)
  e01.set(0)
  e01.set(1)
  b1.push(e01)
  let e12 = Bits::new(3)
  e12.set(1)
  e12.set(2)
  b1.push(e12)
  let e20 = Bits::new(3)
  e20.set(2)
  e20.set(0)
  b1.push(e20)
  let cc = ChainComplex::new([3, 3], [[], b1])
  assert_true(cc.check_d2())
  assert_eq(cc.betti(), [1, 1])
  assert_eq(cc.euler(), 0)
}

///|
test "filtered triangle persistence" {
  // vertices born at 0; edges at 1; face at 2.
  let cells : Array[FilteredCell] = [
    FilteredCell::{ dim: 0, birth: 0, boundary: [], },
    FilteredCell::{ dim: 0, birth: 0, boundary: [], },
    FilteredCell::{ dim: 0, birth: 0, boundary: [], },
    FilteredCell::{ dim: 1, birth: 1, boundary: [0, 1], },
    FilteredCell::{ dim: 1, birth: 1, boundary: [1, 2], },
    FilteredCell::{ dim: 1, birth: 1, boundary: [0, 2], },
    FilteredCell::{ dim: 2, birth: 2, boundary: [3, 4, 5], },
  ]
  let f = Filtration::new(cells)
  let pairs = f.persistence()
  let mut finite0 = 0
  let mut essential = 0
  for p in pairs {
    if p.dim == 0 {
      match p.death {
        Some(_) => finite0 = finite0 + 1
        None => essential = essential + 1
      }
    }
  }
  assert_eq(finite0, 2)
  assert_eq(essential, 1)
  let b0 = f.betti_at(1)
  assert_eq(b0[0], 1)
}

///|
test "finite field arithmetic" {
  assert_eq(fp_add(4, 3, 5), 2)
  assert_eq(fp_mul(3, 4, 5), 2)
  assert_eq(fp_inv(2, 5), 3)
  assert_eq(fp_mul(2, fp_inv(2, 5), 5), 1)
  let m : Array[Array[Int32]] = [[1, 2], [3, 4]]
  assert_eq(fp_det(m, 5), 3)
  assert_eq(fp_rank(m, 5), 2)
  let m2 : Array[Array[Int32]] = [[1, 2], [2, 4]]
  assert_eq(fp_rank(m2, 5), 1)
}
