import R1Z.PV_RDCD3_FieldSource
open Aeneas Aeneas.Std Result ControlFlow Error
namespace R1Z.PV_RDCD3_CB_OwnedMask
def owned.mul_i
  (value : PV_RDCD3_FieldSource.aspis_core.field.CM31) : Result PV_RDCD3_FieldSource.aspis_core.field.CM31 := do
  let m ← PV_RDCD3_FieldSource.aspis_core.field.M31.neg value.b
  PV_RDCD3_FieldSource.aspis_core.field.CM31.new m value.a

/-- [pv_cb_source::owned::mul_r]:
    Source: 'owned.rs', lines 29:0-31:1 -/
def owned.mul_r
  (value : PV_RDCD3_FieldSource.aspis_core.field.CM31) : Result PV_RDCD3_FieldSource.aspis_core.field.CM31 := do
  let m ← PV_RDCD3_FieldSource.aspis_core.field.M31.double value.a
  let m1 ← PV_RDCD3_FieldSource.aspis_core.field.M31.sub m value.b
  let m2 ← PV_RDCD3_FieldSource.aspis_core.field.M31.double value.b
  let m3 ← PV_RDCD3_FieldSource.aspis_core.field.M31.add value.a m2
  PV_RDCD3_FieldSource.aspis_core.field.CM31.new m1 m3

/-- [pv_cb_source::owned::tower]:
    Source: 'owned.rs', lines 32:0-40:1 -/
def owned.tower
  (value : PV_RDCD3_FieldSource.aspis_core.field.QM31) (coordinate : Std.Usize) :
  Result PV_RDCD3_FieldSource.aspis_core.field.QM31
  := do
  match coordinate.val with
  | 0 => ok value
  | 1 =>
    let c ← owned.mul_i value.c0
    let c1 ← owned.mul_i value.c1
    ok { c0 := c, c1 }
  | 2 => let c ← owned.mul_r value.c1
         ok { c0 := c, c1 := value.c0 }
  | 3 =>
    let c ← owned.mul_r value.c1
    let c1 ← owned.mul_i c
    let c2 ← owned.mul_i value.c0
    ok { c0 := c1, c1 := c2 }
  | _ => fail panic

/-- [pv_cb_source::owned::linears_fold]:
    Source: 'owned.rs', lines 41:0-47:1 -/
def owned.linears_fold
  (point : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 10#usize) (variable1 : Std.Usize)
  (suffix : PV_RDCD3_FieldSource.aspis_core.field.QM31) (weighted : PV_RDCD3_FieldSource.aspis_core.field.QM31) :
  Result (PV_RDCD3_FieldSource.aspis_core.field.QM31 × PV_RDCD3_FieldSource.aspis_core.field.QM31)
  := do
  if variable1 > 0#usize
  then
    let variable2 ← lift (Std.Usize.wrapping_sub variable1 1#usize)
    let q ← Array.index_usize point variable2
    let suffix1 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.add suffix q
    let weighted1 ←
      if variable2 != 0#usize
      then PV_RDCD3_FieldSource.aspis_core.field.QM31.add weighted suffix1
      else ok weighted
    owned.linears_fold point variable2 suffix1 weighted1
  else ok (suffix, weighted)
partial_fixpoint

/-- [pv_cb_source::owned::linears]:
    Source: 'owned.rs', lines 48:0-52:1 -/
def owned.linears
  (point : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 10#usize) :
  Result (PV_RDCD3_FieldSource.aspis_core.field.QM31 × PV_RDCD3_FieldSource.aspis_core.field.QM31)
  := do
  let (suffix, weighted) ←
    owned.linears_fold point 10#usize PV_RDCD3_FieldSource.aspis_core.field.QM31.ZERO
      PV_RDCD3_FieldSource.aspis_core.field.QM31.ZERO
  let q ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul_m31 suffix 3#u32
  let q1 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul_m31 weighted 22#u32
  let q2 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.add q q1
  let q3 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul_m31 suffix 275#u32
  let q4 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul_m31 weighted 150#u32
  let q5 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.add q3 q4
  ok (q2, q5)

/-- [pv_cb_source::owned::cell]:
    Source: 'owned.rs', lines 53:0-53:83 -/
def owned.cell
  (out : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize) (index : Std.Usize)
  (value : PV_RDCD3_FieldSource.aspis_core.field.QM31) :
  Result (Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize)
  := do
  Array.update out index value

/-- [pv_cb_source::owned::fill_c1]:
    Source: 'owned.rs', lines 54:0-59:1 -/
def owned.fill_c1
  (c1 : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 16#usize)
  (coefficients : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize) (column : Std.Usize) :
  Result (Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize)
  := do
  if column < 16#usize
  then
    let i ←
      Array.index_usize
        (Array.make 16#usize [
          0#usize, 2#usize, 4#usize, 6#usize, 8#usize, 10#usize, 12#usize,
          14#usize, 16#usize, 18#usize, 20#usize, 22#usize, 24#usize, 26#usize,
          13#usize, 25#usize
          ]) column
    let q ← Array.index_usize c1 column
    let i1 ← lift (column &&& 3#usize)
    let q1 ← owned.tower q i1
    let a ← owned.cell coefficients i q1
    let i2 ← lift (Std.Usize.wrapping_add column 1#usize)
    owned.fill_c1 c1 a i2
  else ok coefficients
partial_fixpoint

/-- [pv_cb_source::owned::fill_mask]:
    Source: 'owned.rs', lines 60:0-65:1 -/
def owned.fill_mask
  (mask : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 10#usize)
  (coefficients : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize) (column : Std.Usize) :
  Result (Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize)
  := do
  if column < 10#usize
  then
    let i ←
      Array.index_usize
        (Array.make 10#usize [
          1#usize, 3#usize, 5#usize, 7#usize, 9#usize, 11#usize, 15#usize,
          17#usize, 19#usize, 21#usize
          ]) column
    let q ← Array.index_usize mask column
    let i1 ← lift (column &&& 3#usize)
    let q1 ← owned.tower q i1
    let a ← owned.cell coefficients i q1
    let i2 ← lift (Std.Usize.wrapping_add column 1#usize)
    owned.fill_mask mask a i2
  else ok coefficients
partial_fixpoint

/-- [pv_cb_source::owned::horner]:
    Source: 'owned.rs', lines 66:0-71:1 -/
def owned.horner
  (coefficients : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 27#usize)
  (prepared : PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier) (exponent : Std.Usize)
  (shared : PV_RDCD3_FieldSource.aspis_core.field.QM31) :
  Result PV_RDCD3_FieldSource.aspis_core.field.QM31
  := do
  if exponent > 0#usize
  then
    let exponent1 ← lift (Std.Usize.wrapping_sub exponent 1#usize)
    let q ← PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.mul prepared shared
    let q1 ← Array.index_usize coefficients exponent1
    let q2 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.add q q1
    owned.horner coefficients prepared exponent1 q2
  else ok shared
partial_fixpoint

/-- [pv_cb_source::owned::mask]:
    Source: 'owned.rs', lines 72:0-80:1
    Visibility: public -/
def owned.mask
  (c1 : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 16#usize)
  (mask_only : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 10#usize)
  (g : PV_RDCD3_FieldSource.aspis_core.field.QM31) (point : Array PV_RDCD3_FieldSource.aspis_core.field.QM31 10#usize) :
  Result PV_RDCD3_FieldSource.aspis_core.field.QM31
  := do
  let (linear, explicit_linear) ← owned.linears point
  let a := Array.repeat 27#usize PV_RDCD3_FieldSource.aspis_core.field.QM31.ZERO
  let coefficients ← owned.fill_c1 c1 a 0#usize
  let coefficients1 ← owned.fill_mask mask_only coefficients 0#usize
  let prepared ← PV_RDCD3_FieldSource.aspis_core.field.PreparedQm31Multiplier.new linear
  let q ← Array.index_usize coefficients1 26#usize
  let shared ← owned.horner coefficients1 prepared 26#usize q
  let x2 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.square explicit_linear
  let x4 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.square x2
  let x8 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.square x4
  let x16 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.square x8
  let q1 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul x16 x8
  let q2 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul q1 x2
  let q3 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.add PV_RDCD3_FieldSource.aspis_core.field.QM31.ONE q2
  let q4 ← PV_RDCD3_FieldSource.aspis_core.field.QM31.mul q3 g
  PV_RDCD3_FieldSource.aspis_core.field.QM31.add shared q4

end R1Z.PV_RDCD3_CB_OwnedMask
