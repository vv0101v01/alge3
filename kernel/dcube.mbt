///|
// Dimension-free affine cubical `DCube` / `DOpenBox` Kan composition
// (works without De Morgan connection operators `DAnd` / `DOr`).

///|
pub struct DCube {
  dim : Int32
  eval : (Array[Dim]) -> DValue
}

///|
pub struct DOpenBoxFace {
  axis : Int32
  dir : Bool
  face_cube : DCube
}

///|
pub struct DOpenBox {
  ty : DValue
  dim : Int32
  dlevel : Int32
  faces : Array[DOpenBoxFace]
}

///|
pub fn dcube_constant(dim : Int32, v : DValue) -> DCube {
  DCube::{ dim, eval: _ => v, }
}

///|
pub fn dcube_of_path(f : (Dim) -> DValue) -> DCube {
  DCube::{
    dim: 1,
    eval: coords => if coords.length() > 0 { f(coords[0]) } else { f(DZero) },
  }
}

///|
pub fn dcube_at(cube : DCube, coords : Array[Dim]) -> DValue {
  (cube.eval)(coords)
}

///|
pub fn dcube_box_face(
  axis : Int32,
  dir : Bool,
  face_cube : DCube,
) -> DOpenBoxFace {
  DOpenBoxFace::{ axis, dir, face_cube, }
}

///|
pub fn dcube_open_box(
  ty : DValue,
  dim : Int32,
  dlevel : Int32,
  faces : Array[DOpenBoxFace],
) -> DOpenBox {
  DOpenBox::{ ty, dim, dlevel, faces, }
}

///|
fn box_find_face(box : DOpenBox, axis : Int32, dir : Bool) -> DOpenBoxFace? {
  for f in box.faces {
    if f.axis == axis && f.dir == dir {
      return Some(f)
    }
  }
  None
}

///|
fn box_find_missing_cap(box : DOpenBox) -> (Int32, Bool)? {
  let mut missing : (Int32, Bool)? = None
  let mut count = 0
  for ax in 0..<box.dim {
    for dir in [false, true] {
      if box_find_face(box, ax, dir) is None {
        missing = Some((ax, dir))
        count = count + 1
      }
    }
  }
  if count == 1 {
    missing
  } else {
    None
  }
}

///|
fn remove_axis(coords : Array[Dim], axis : Int32) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<coords.length() {
    if i != axis {
      out.push(coords[i])
    }
  }
  out
}

///|
fn insert_axis(coords : Array[Dim], axis : Int32, val : Dim) -> Array[Dim] {
  let out : Array[Dim] = []
  for i in 0..<coords.length() {
    if i == axis {
      out.push(val)
    }
    out.push(coords[i])
  }
  if axis == coords.length() {
    out.push(val)
  }
  out
}

///|
fn max_var_in_coords(coords : Array[Dim]) -> Int32 {
  let mut mv = -1
  for c in coords {
    let nv = dim_nvars_sem(c)
    if nv - 1 > mv {
      mv = nv - 1
    }
  }
  mv
}

///|
fn box_corners_compatible(box : DOpenBox, level : Int32) -> Bool {
  let n = box.faces.length()
  let rem_dim = box.dim - 2
  if rem_dim < 0 {
    return true
  }
  let base_dl = box.dlevel + box.dim + 4
  let rem_vars : Array[Dim] = []
  for k in 0..<rem_dim {
    rem_vars.push(Dim::DVar(base_dl + k))
  }
  for i in 0..<n {
    for j in (i + 1)..<n {
      let fi = box.faces[i]
      let fj = box.faces[j]
      if fi.axis < fj.axis {
        // Build the shared (dim - 2)-face embedded in full coordinates, then project to fi and fj
        let mut ci = insert_axis(
          rem_vars,
          fj.axis,
          if fj.dir {
            DOne
          } else {
            DZero
          },
        )
        let full = insert_axis(ci, fi.axis, if fi.dir { DOne } else { DZero })
        ci = remove_axis(full, fi.axis)
        let cj = remove_axis(full, fj.axis)
        if !conv_at(
            level,
            base_dl + rem_dim,
            box.ty,
            dcube_at(fi.face_cube, ci),
            dcube_at(fj.face_cube, cj),
          ) {
          return false
        }
      } else if fj.axis < fi.axis {
        let mut cj = insert_axis(
          rem_vars,
          fi.axis,
          if fi.dir {
            DOne
          } else {
            DZero
          },
        )
        let full = insert_axis(cj, fj.axis, if fj.dir { DOne } else { DZero })
        cj = remove_axis(full, fj.axis)
        let ci = remove_axis(full, fi.axis)
        if !conv_at(
            level,
            base_dl + rem_dim,
            box.ty,
            dcube_at(fi.face_cube, ci),
            dcube_at(fj.face_cube, cj),
          ) {
          return false
        }
      }
    }
  }
  true
}

///|
fn box_solve_at(
  box : DOpenBox,
  cap_axis : Int32,
  cap_dir : Bool,
  base_face : DOpenBoxFace,
  full_coords : Array[Dim],
) -> DValue {
  let coords_wo_cap = remove_axis(full_coords, cap_axis)
  let base_val = dcube_at(base_face.face_cube, coords_wo_cap)
  let branches : Array[DTubeBranch] = []
  for f in box.faces {
    if f.axis != cap_axis {
      let face = if f.dir {
        face_simplify(FEq1(full_coords[f.axis]))
      } else {
        face_simplify(FEq0(full_coords[f.axis]))
      }
      if !face_is_bot_sem(face) {
        let path = fn(j : Dim) -> DValue {
          let j_coord = if cap_dir { j } else { dim_simplify(DNeg(j)) }
          let full_j = insert_axis(coords_wo_cap, cap_axis, j_coord)
          dcube_at(f.face_cube, remove_axis(full_j, f.axis))
        }
        branches.push(tube_branch(face, path))
      }
    }
  }
  let sys = dsystem_of(branches)
  let mv = max_var_in_coords(full_coords)
  let comp_dl = if box.dlevel > mv + 1 { box.dlevel } else { mv + 1 }
  let raw_t = full_coords[cap_axis]
  let t = if cap_dir { raw_t } else { dim_simplify(DNeg(raw_t)) }
  hfill_value(box.ty, sys, base_val, comp_dl)(t)
}

///|
pub fn dcube_box_fill_verified(box : DOpenBox, level : Int32) -> DCube? {
  match box_find_missing_cap(box) {
    Some((cap_axis, cap_dir)) =>
      match box_find_face(box, cap_axis, !cap_dir) {
        Some(base_face) => {
          if !box_corners_compatible(box, level) {
            return None
          }
          Some(DCube::{
            dim: box.dim,
            eval: coords => {
              box_solve_at(box, cap_axis, cap_dir, base_face, coords)
            },
          })
        }
        None => None
      }
    None => None
  }
}

///|
pub fn dcube_box_cap(box : DOpenBox) -> DCube? {
  match box_find_missing_cap(box) {
    Some((cap_axis, cap_dir)) =>
      match box_find_face(box, cap_axis, !cap_dir) {
        Some(base_face) => {
          let cap_dim_val = if cap_dir { Dim::DOne } else { Dim::DZero }
          Some(DCube::{
            dim: box.dim - 1,
            eval: cap_coords => {
              let full = insert_axis(cap_coords, cap_axis, cap_dim_val)
              box_solve_at(box, cap_axis, cap_dir, base_face, full)
            },
          })
        }
        None => None
      }
    None => None
  }
}

///|
pub fn dcube_filler_faces_ok(
  box : DOpenBox,
  filler : DCube,
  level : Int32,
) -> Bool {
  let rem_dim = box.dim - 1
  let dl = box.dlevel
  let rem_vars : Array[Dim] = []
  for k in 0..<rem_dim {
    rem_vars.push(Dim::DVar(dl + k))
  }
  for f in box.faces {
    let full = insert_axis(rem_vars, f.axis, if f.dir { DOne } else { DZero })
    let got = dcube_at(filler, full)
    let want = dcube_at(f.face_cube, rem_vars)
    if !conv_at(level, dl + rem_dim, box.ty, got, want) {
      return false
    }
  }
  true
}
