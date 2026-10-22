import MultiproofConeOpeningRows

set_option autoImplicit false
namespace AspisR1.MultiproofConeSliceComposition
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft
open MultiproofConeOpeningRows

private theorem drop_take_eq (xs : Bytes) (start width : Nat) :
    (xs.take width).drop start = (xs.drop start).take (width-start) := by
  induction start generalizing xs width with
  | zero => simp
  | succ start ih =>
    cases width with
    | zero => simp
    | succ width =>
      cases xs with
      | nil => simp
      | cons a xs =>
        simpa only [List.take_succ_cons,List.drop_succ_cons,Nat.succ_sub_succ_eq_sub]
          using ih xs width

private theorem take_take_le (xs : Bytes) (small large : Nat) (bound : small ≤ large) :
    (xs.take large).take small = xs.take small := by
  induction small generalizing xs large with
  | zero => rfl
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      cases xs with
      | nil => rfl
      | cons a xs =>
        simpa only [List.take_succ_cons] using congrArg (List.cons a) (ih xs large (by omega))

theorem slice_slice (wire : Bytes) (base width offset size : Nat)
    (bound : offset+size ≤ width) :
    slice (slice wire base width) offset size = slice wire (base+offset) size := by
  unfold slice
  rw [drop_take_eq, take_take_le _ size (width-offset) (by omega), List.drop_drop]

theorem all_slice (wire : Bytes) (base count : Nat) :
    AllOpenings count (slice wire base (832*count)) ↔
      ∀ j, j<count → openingCanonical (slice wire (base+832*j) 832) := by
  constructor
  · intro all j hj
    have h := all j hj
    rw [slice_slice wire base (832*count) (832*j) 832 (by omega)] at h
    exact h
  · intro all j hj
    rw [slice_slice wire base (832*count) (832*j) 832 (by omega)]
    exact all j hj

#print axioms drop_take_eq
#print axioms take_take_le
#print axioms slice_slice
#print axioms all_slice
end AspisR1.MultiproofConeSliceComposition
