import PV_B3_MaskDictionary134
import PV_B3_Range117
import PV_B3_Copy_117_Funs
import PV_B3_Result
import PV_B3_PrefixRank222
import PV_B3_BoundedLoop
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_B3_Copy_117
def host_arithmetic.accumulate_channels
  (sums : Array (Array Std.U64 3#usize) 3#usize) (left : aspis_core.field.QM31)
  (right : aspis_core.field.QM31) :
  Result (Array (Array Std.U64 3#usize) 3#usize)
  := do
  let left_sum ← aspis_core.field.CM31.add left.c0 left.c1
  let right_sum ← aspis_core.field.CM31.add right.c0 right.c1
  let m ← aspis_core.field.M31.add left.c0.a left.c0.b
  let m1 ← aspis_core.field.M31.add left.c1.a left.c1.b
  let m2 ← aspis_core.field.M31.add left_sum.a left_sum.b
  let m3 ← aspis_core.field.M31.add right.c0.a right.c0.b
  let m4 ← aspis_core.field.M31.add right.c1.a right.c1.b
  let m5 ← aspis_core.field.M31.add right_sum.a right_sum.b
  let a ←
    Array.index_usize
      (Array.make 3#usize [
        (Array.make 3#usize [ left.c0.a, left.c0.b, m ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ left.c1.a, left.c1.b, m1 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ left_sum.a, left_sum.b, m2 ] : Array
        aspis_core.field.M31 3#usize)
        ]) 0#usize
  let m6 ← Array.index_usize a 0#usize
  let i ← lift (UScalar.cast .U64 m6)
  let a1 ←
    Array.index_usize
      (Array.make 3#usize [
        (Array.make 3#usize [ right.c0.a, right.c0.b, m3 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right.c1.a, right.c1.b, m4 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right_sum.a, right_sum.b, m5 ] : Array
        aspis_core.field.M31 3#usize)
        ]) 0#usize
  let m7 ← Array.index_usize a1 0#usize
  let i1 ← lift (UScalar.cast .U64 m7)
  let i2 ← lift (Std.U64.wrapping_mul i i1)
  let a2 ← Array.index_usize sums 0#usize
  let i3 ← Array.index_usize a2 0#usize
  let i4 ← lift (Std.U64.wrapping_add i3 i2)
  let (a3, index_mut_back) ← Array.index_mut_usize sums 0#usize
  let a4 ← Array.update a3 0#usize i4
  let m8 ← Array.index_usize a 1#usize
  let i5 ← lift (UScalar.cast .U64 m8)
  let m9 ← Array.index_usize a1 1#usize
  let i6 ← lift (UScalar.cast .U64 m9)
  let i7 ← lift (Std.U64.wrapping_mul i5 i6)
  let sums1 := index_mut_back a4
  let a5 ← Array.index_usize sums1 0#usize
  let i8 ← Array.index_usize a5 1#usize
  let i9 ← lift (Std.U64.wrapping_add i8 i7)
  let (a6, index_mut_back1) ← Array.index_mut_usize sums1 0#usize
  let a7 ← Array.update a6 1#usize i9
  let m10 ← Array.index_usize a 2#usize
  let i10 ← lift (UScalar.cast .U64 m10)
  let m11 ← Array.index_usize a1 2#usize
  let i11 ← lift (UScalar.cast .U64 m11)
  let i12 ← lift (Std.U64.wrapping_mul i10 i11)
  let sums2 := index_mut_back1 a7
  let a8 ← Array.index_usize sums2 0#usize
  let i13 ← Array.index_usize a8 2#usize
  let i14 ← lift (Std.U64.wrapping_add i13 i12)
  let (a9, index_mut_back2) ← Array.index_mut_usize sums2 0#usize
  let a10 ← Array.update a9 2#usize i14
  let a11 ←
    Array.index_usize
      (Array.make 3#usize [
        (Array.make 3#usize [ left.c0.a, left.c0.b, m ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ left.c1.a, left.c1.b, m1 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ left_sum.a, left_sum.b, m2 ] : Array
        aspis_core.field.M31 3#usize)
        ]) 1#usize
  let m12 ← Array.index_usize a11 0#usize
  let i15 ← lift (UScalar.cast .U64 m12)
  let a12 ←
    Array.index_usize
      (Array.make 3#usize [
        (Array.make 3#usize [ right.c0.a, right.c0.b, m3 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right.c1.a, right.c1.b, m4 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right_sum.a, right_sum.b, m5 ] : Array
        aspis_core.field.M31 3#usize)
        ]) 1#usize
  let m13 ← Array.index_usize a12 0#usize
  let i16 ← lift (UScalar.cast .U64 m13)
  let i17 ← lift (Std.U64.wrapping_mul i15 i16)
  let sums3 := index_mut_back2 a10
  let a13 ← Array.index_usize sums3 1#usize
  let i18 ← Array.index_usize a13 0#usize
  let i19 ← lift (Std.U64.wrapping_add i18 i17)
  let (a14, index_mut_back3) ← Array.index_mut_usize sums3 1#usize
  let a15 ← Array.update a14 0#usize i19
  let m14 ← Array.index_usize a11 1#usize
  let i20 ← lift (UScalar.cast .U64 m14)
  let m15 ← Array.index_usize a12 1#usize
  let i21 ← lift (UScalar.cast .U64 m15)
  let i22 ← lift (Std.U64.wrapping_mul i20 i21)
  let sums4 := index_mut_back3 a15
  let a16 ← Array.index_usize sums4 1#usize
  let i23 ← Array.index_usize a16 1#usize
  let i24 ← lift (Std.U64.wrapping_add i23 i22)
  let (a17, index_mut_back4) ← Array.index_mut_usize sums4 1#usize
  let a18 ← Array.update a17 1#usize i24
  let m16 ← Array.index_usize a11 2#usize
  let i25 ← lift (UScalar.cast .U64 m16)
  let m17 ← Array.index_usize a12 2#usize
  let i26 ← lift (UScalar.cast .U64 m17)
  let i27 ← lift (Std.U64.wrapping_mul i25 i26)
  let sums5 := index_mut_back4 a18
  let a19 ← Array.index_usize sums5 1#usize
  let i28 ← Array.index_usize a19 2#usize
  let i29 ← lift (Std.U64.wrapping_add i28 i27)
  let (a20, index_mut_back5) ← Array.index_mut_usize sums5 1#usize
  let a21 ← Array.update a20 2#usize i29
  let a22 ←
    Array.index_usize
      (Array.make 3#usize [
        (Array.make 3#usize [ left.c0.a, left.c0.b, m ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ left.c1.a, left.c1.b, m1 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ left_sum.a, left_sum.b, m2 ] : Array
        aspis_core.field.M31 3#usize)
        ]) 2#usize
  let m18 ← Array.index_usize a22 0#usize
  let i30 ← lift (UScalar.cast .U64 m18)
  let a23 ←
    Array.index_usize
      (Array.make 3#usize [
        (Array.make 3#usize [ right.c0.a, right.c0.b, m3 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right.c1.a, right.c1.b, m4 ] : Array
        aspis_core.field.M31 3#usize),
        (Array.make 3#usize [ right_sum.a, right_sum.b, m5 ] : Array
        aspis_core.field.M31 3#usize)
        ]) 2#usize
  let m19 ← Array.index_usize a23 0#usize
  let i31 ← lift (UScalar.cast .U64 m19)
  let i32 ← lift (Std.U64.wrapping_mul i30 i31)
  let sums6 := index_mut_back5 a21
  let a24 ← Array.index_usize sums6 2#usize
  let i33 ← Array.index_usize a24 0#usize
  let i34 ← lift (Std.U64.wrapping_add i33 i32)
  let (a25, index_mut_back6) ← Array.index_mut_usize sums6 2#usize
  let a26 ← Array.update a25 0#usize i34
  let m20 ← Array.index_usize a22 1#usize
  let i35 ← lift (UScalar.cast .U64 m20)
  let m21 ← Array.index_usize a23 1#usize
  let i36 ← lift (UScalar.cast .U64 m21)
  let i37 ← lift (Std.U64.wrapping_mul i35 i36)
  let sums7 := index_mut_back6 a26
  let a27 ← Array.index_usize sums7 2#usize
  let i38 ← Array.index_usize a27 1#usize
  let i39 ← lift (Std.U64.wrapping_add i38 i37)
  let (a28, index_mut_back7) ← Array.index_mut_usize sums7 2#usize
  let a29 ← Array.update a28 1#usize i39
  let m22 ← Array.index_usize a22 2#usize
  let i40 ← lift (UScalar.cast .U64 m22)
  let m23 ← Array.index_usize a23 2#usize
  let i41 ← lift (UScalar.cast .U64 m23)
  let i42 ← lift (Std.U64.wrapping_mul i40 i41)
  let sums8 := index_mut_back7 a29
  let a30 ← Array.index_usize sums8 2#usize
  let i43 ← Array.index_usize a30 2#usize
  let i44 ← lift (Std.U64.wrapping_add i43 i42)
  let (a31, index_mut_back8) ← Array.index_mut_usize sums8 2#usize
  let a32 ← Array.update a31 2#usize i44
  ok (index_mut_back8 a32)

def host_arithmetic.reconstruct_component
  (channels : Array Std.U64 3#usize) : Result aspis_core.field.CM31 := do
  let i ← Array.index_usize channels 0#usize
  let m0 ← aspis_core.field.M31.reduce_u64 i
  let i1 ← Array.index_usize channels 1#usize
  let m1 ← aspis_core.field.M31.reduce_u64 i1
  let i2 ← Array.index_usize channels 2#usize
  let m2 ← aspis_core.field.M31.reduce_u64 i2
  let m ← aspis_core.field.M31.sub m0 m1
  let m3 ← aspis_core.field.M31.sub m2 m0
  let m4 ← aspis_core.field.M31.sub m3 m1
  ok { a := m, b := m4 }

def host_arithmetic.reconstruct_channels
  (sums : Array (Array Std.U64 3#usize) 3#usize) :
  Result aspis_core.field.QM31
  := do
  let a ← Array.index_usize sums 0#usize
  let m0 ← host_arithmetic.reconstruct_component a
  let a1 ← Array.index_usize sums 1#usize
  let m1 ← host_arithmetic.reconstruct_component a1
  let a2 ← Array.index_usize sums 2#usize
  let m2 ← host_arithmetic.reconstruct_component a2
  let c ← host_arithmetic.cm31_mul_r m1
  let c1 ← aspis_core.field.CM31.add m0 c
  let c2 ← aspis_core.field.CM31.sub m2 m0
  let c3 ← aspis_core.field.CM31.sub c2 m1
  ok { c0 := c1, c1 := c3 }

def host_arithmetic.qm31_sum_products3
  (left : Array aspis_core.field.QM31 3#usize)
  (right : Array aspis_core.field.QM31 3#usize) :
  Result aspis_core.field.QM31
  := do
  let a := Array.repeat 3#usize 0#u64
  let a1 := Array.repeat 3#usize a
  let q ← Array.index_usize left 0#usize
  let q1 ← Array.index_usize right 0#usize
  let sums ← host_arithmetic.accumulate_channels a1 q q1
  let q2 ← Array.index_usize left 1#usize
  let q3 ← Array.index_usize right 1#usize
  let sums1 ← host_arithmetic.accumulate_channels sums q2 q3
  let q4 ← Array.index_usize left 2#usize
  let q5 ← Array.index_usize right 2#usize
  let sums2 ← host_arithmetic.accumulate_channels sums1 q4 q5
  host_arithmetic.reconstruct_channels sums2

def host_arithmetic.evaluate_state_only_polynomial.block_value
  (polynomial : Array aspis_core.field.QM31 28#usize)
  (powers : Array aspis_core.field.QM31 3#usize) (block : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  let start ← lift (Std.Usize.wrapping_mul 4#usize block)
  let q ← Array.index_usize polynomial start
  let i ← lift (Std.Usize.wrapping_add start 1#usize)
  let q1 ← Array.index_usize polynomial i
  let i1 ← lift (Std.Usize.wrapping_add start 2#usize)
  let q2 ← Array.index_usize polynomial i1
  let i2 ← lift (Std.Usize.wrapping_add start 3#usize)
  let q3 ← Array.index_usize polynomial i2
  let q4 ←
    host_arithmetic.qm31_sum_products3 powers
      (Array.make 3#usize [ q1, q2, q3 ])
  aspis_core.field.QM31.add q q4

def host_arithmetic.evaluate_state_only_polynomial_loop.body
  (polynomial : Array aspis_core.field.QM31 28#usize)
  (powers : Array aspis_core.field.QM31 3#usize)
  (prepared_x4 : host_arithmetic.PreparedQm31Multiplier)
  (accumulator : aspis_core.field.QM31) (block : Std.Usize) :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31)
  := do
  if block > 0#usize
  then
    let block1 ← lift (Std.Usize.wrapping_sub block 1#usize)
    let q ←
      host_arithmetic.PreparedQm31Multiplier.mul prepared_x4 accumulator
    let q1 ←
      host_arithmetic.evaluate_state_only_polynomial.block_value polynomial
        powers block1
    let accumulator1 ← aspis_core.field.QM31.add q q1
    ok (cont (accumulator1, block1))
  else ok (done accumulator)

def host_arithmetic.evaluate_state_only_polynomial_loop
  (polynomial : Array aspis_core.field.QM31 28#usize)
  (powers : Array aspis_core.field.QM31 3#usize)
  (prepared_x4 : host_arithmetic.PreparedQm31Multiplier)
  (accumulator : aspis_core.field.QM31) (block : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (accumulator1, block1) =>
      host_arithmetic.evaluate_state_only_polynomial_loop.body polynomial
      powers prepared_x4 accumulator1 block1)
    (accumulator, block)

def host_arithmetic.evaluate_state_only_polynomial
  (polynomial : Array aspis_core.field.QM31 28#usize)
  (challenge : aspis_core.field.QM31) :
  Result aspis_core.field.QM31
  := do
  let x2 ← aspis_core.field.QM31.square challenge
  let x3 ← aspis_core.field.QM31.mul challenge x2
  let x4 ← aspis_core.field.QM31.square x2
  let prepared_x4 ← host_arithmetic.PreparedQm31Multiplier.new x4
  let accumulator ←
    host_arithmetic.evaluate_state_only_polynomial.block_value polynomial
      (Array.make 3#usize [ challenge, x2, x3 ]) 6#usize
  host_arithmetic.evaluate_state_only_polynomial_loop polynomial
    (Array.make 3#usize [ challenge, x2, x3 ]) prepared_x4 accumulator 6#usize

#print axioms host_arithmetic.accumulate_channels
#print axioms host_arithmetic.reconstruct_component
#print axioms host_arithmetic.reconstruct_channels
#print axioms host_arithmetic.qm31_sum_products3
#print axioms host_arithmetic.evaluate_state_only_polynomial.block_value
#print axioms host_arithmetic.evaluate_state_only_polynomial_loop.body
#print axioms host_arithmetic.evaluate_state_only_polynomial_loop
#print axioms host_arithmetic.evaluate_state_only_polynomial
end PV_B3_Copy_117

namespace PV_B3_AuditSourceD324.Errors134
open Aeneas Aeneas.Std Result PV_B3_MaskDictionary134
set_option autoImplicit false

def restoreError : OldError → NewError
  | .Shape => .Shape
  | .EndpointCapacity row => .EndpointCapacity row

def restore : Result OldFinal → Result NewFinal
  | .ok (.Ok m) => .ok (.Ok m)
  | .ok (.Err e) => .ok (.Err (restoreError e))
  | .fail e => .fail e
  | .div => .div

theorem error_roundtrip (e : NewError) : restoreError (error e) = e := by
  cases e <;> rfl

theorem reverse_error_roundtrip (e : OldError) : error (restoreError e) = e := by
  cases e <;> rfl

theorem roundtrip (r : Result NewFinal) : restore (translate r) = r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok value =>
    cases value with
    | Ok m => rfl
    | Err e => simp only [translate, restore, error_roundtrip]

theorem reverse_roundtrip (r : Result OldFinal) : translate (restore r) = r := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok value =>
    cases value with
    | Ok m => rfl
    | Err e => simp only [translate, restore, reverse_error_roundtrip]

theorem injective : Function.Injective translate := by
  intro a b h
  have eq := congrArg restore h
  simpa only [roundtrip] using eq

theorem no_hidden_success (r : Result NewFinal) (m : Array U16 64#usize) :
    translate r = ok (.Ok m) ↔ r = ok (.Ok m) := by
  constructor
  · intro h
    apply injective
    exact h
  · intro h
    rw [h]
    rfl

#print axioms restoreError
#print axioms restore
#print axioms error_roundtrip
#print axioms reverse_error_roundtrip
#print axioms roundtrip
#print axioms reverse_roundtrip
#print axioms injective
#print axioms no_hidden_success
end PV_B3_AuditSourceD324.Errors134

namespace PV_B3_AuditSourceD324.Mask117
open Aeneas Aeneas.Std Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31

def reference (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) : Result Q := do
  let (linear, explicit_linear) ← host_arithmetic.selected_mask_linears point
  let coefficients ← PV_B3_Range117.scatter c1 host_arithmetic.FACTOR_EXPONENTS
    PV_B3_Range117.selectedIndices (Array.repeat 27#usize aspis_core.field.QM31.ZERO)
  let coefficients ← PV_B3_Range117.scatter mask host_arithmetic.MASK_ONLY_FACTOR_EXPONENTS
    PV_B3_Range117.maskIndices coefficients
  let shared ← (do
    let prepared ← host_arithmetic.PreparedQm31Multiplier.new linear
    let shared ← Array.index_usize coefficients
      aspis_core.state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
    PV_B3_Range117.horner coefficients prepared PV_B3_Range117.hornerIndices shared)
  let power ← host_arithmetic.mask_power_26 explicit_linear
  let factor ← aspis_core.field.QM31.add aspis_core.field.QM31.ONE power
  let explicit_value ← aspis_core.field.QM31.mul factor g
  aspis_core.field.QM31.add shared explicit_value

theorem source (c1 : Array Q 16#usize) (mask : Array Q 10#usize)
    (g : Q) (point : Array Q 10#usize) :
    host_arithmetic.state_only_selected_mask_value c1 mask g point =
      reference c1 mask g point := by
  unfold host_arithmetic.state_only_selected_mask_value reference
  simp_rw [PV_B3_Range117.selected, PV_B3_Range117.mask_only,
    PV_B3_Range117.prepared_horner]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨linear, explicit_linear⟩ h
  with_unfolding_all rfl

#print axioms reference
#print axioms source
end PV_B3_AuditSourceD324.Mask117

namespace PV_B3_AuditSourceD324.Poly121
open Aeneas Aeneas.Std Result ControlFlow PV_B3_Result PV_B3_Copy_117
set_option autoImplicit false
abbrev Q := aspis_core.field.QM31
abbrev State := Q × Usize
 def Progress (i : Usize) : ControlFlow State Q → Prop
 | .done _ => True
 | .cont s => s.2 = Usize.wrapping_sub i 1#usize
 theorem body_counter (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) :
    Safe (Progress i) (host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p a i) := by
  unfold host_arithmetic.evaluate_state_only_polynomial_loop.body
  simp only [lift,bind_tc_ok]
  split
  · apply bind_any
    intro q
    apply bind_any
    intro block_value
    apply bind_any
    intro accumulator
    intro cf h
    cases h
    rfl
  · intro cf h
    cases h
    trivial

 def rank (s : State) : Nat := s.2.val
 theorem rank_step (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) (next : State)
    (h : host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p a i = ok (cont next)) :
    rank next < rank (a,i) := by
  have hc := body_counter poly powers p a i (cont next) h
  change next.2 = Usize.wrapping_sub i 1#usize at hc
  have hi : 0 < i.val := by
    unfold host_arithmetic.evaluate_state_only_polynomial_loop.body at h
    split at h
    · assumption
    · cases h
  unfold rank
  dsimp only
  rw [hc,PV_B3_PrefixRank222.decrement i hi]
  omega

 def body (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (s : State) : Result (ControlFlow State Q) :=
    host_arithmetic.evaluate_state_only_polynomial_loop.body poly powers p s.1 s.2
 theorem decreases (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (s t : State)
    (h : body poly powers p s = ok (cont t)) : rank t < rank s := by
  rcases s with ⟨a,i⟩
  exact rank_step poly powers p a i t h
 theorem loop_source (poly : Array Q 28#usize) (powers : Array Q 3#usize)
    (p : host_arithmetic.PreparedQm31Multiplier) (a : Q) (i : Usize) :
    host_arithmetic.evaluate_state_only_polynomial_loop poly powers p a i =
      PV_B3_BoundedLoop.bounded (body poly powers p) i.val (a,i) := by
  exact PV_B3_BoundedLoop.source_eq_bounded (body poly powers p) rank
    (decreases poly powers p) i.val (a,i) (Nat.le_refl _)
 def reference (poly : Array Q 28#usize) (x : Q) : Result Q := do
  let x2 ← aspis_core.field.QM31.square x
  let x3 ← aspis_core.field.QM31.mul x x2
  let x4 ← aspis_core.field.QM31.square x2
  let p ← host_arithmetic.PreparedQm31Multiplier.new x4
  let powers := Array.make 3#usize [x,x2,x3]
  let a ← host_arithmetic.evaluate_state_only_polynomial.block_value poly powers 6#usize
  PV_B3_BoundedLoop.bounded (body poly powers p) 6 (a,6#usize)
 theorem source_complete (poly : Array Q 28#usize) (x : Q) :
    host_arithmetic.evaluate_state_only_polynomial poly x = reference poly x := by
  unfold host_arithmetic.evaluate_state_only_polynomial reference
  simp only [loop_source]
  rfl

#print axioms Progress
#print axioms body_counter
#print axioms rank
#print axioms rank_step
#print axioms body
#print axioms decreases
#print axioms loop_source
#print axioms reference
#print axioms source_complete
end PV_B3_AuditSourceD324.Poly121
