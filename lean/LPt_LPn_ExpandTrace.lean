import LPt_LPn_ExpandSpatial
open Aeneas Aeneas.Std Result LPt_LPl_Kit_Release
set_option autoImplicit false
namespace LPt_LPn.Expand

/-- The reached source loop: exactly one local observation per selected byte
    and one next-row event. K012 supplies actual window identity/count/end;
    K001 supplies these byte observations via local_global. -/
inductive NativeTrace (bs initial : List U8) : Nat → List U8 → Prop where
  | start : NativeTrace bs initial 0 initial
  | next (row : Nat) (before after : List U8)
      (rest : NativeTrace bs initial row before)
      (size : after.length=before.length)
      (observed : ∀ j, j<before.length → after[j]?.getD 0#u8 =
        localByte (fun lane => bs[16*row+lane]?.getD 0#u8)
          (before[j]?.getD 0#u8) (coordinate row j)) :
      NativeTrace bs initial (row+1) after

theorem to_inherited (bs initial after : List U8) (n : Nat)
    (trace : NativeTrace bs initial n after) : LPt_LPl.Expand.Trace bs initial n after := by
  induction trace with
  | start => exact .start
  | next row before after rest size observed ih =>
    exact .next row before after ih (write_of_observations bs before after row size observed)

theorem of_inherited (bs initial after : List U8) (n : Nat)
    (trace : LPt_LPl.Expand.Trace bs initial n after) : NativeTrace bs initial n after := by
  induction trace with
  | start => exact .start
  | next row before after rest write ih =>
    apply NativeTrace.next row before after ih write.length
    intro j hj
    exact (write.bytes j hj).trans (local_global bs before row j).symm

theorem total (bs initial : List U8) (n : Nat) :
    ∃ after, NativeTrace bs initial n after := by
  obtain ⟨after,trace⟩ := LPt_LPl.Expand.total bs initial n
  exact ⟨after,of_inherited bs initial after n trace⟩

theorem native_result (bs before after : Slice U8)
    (bound : bs.val.length≤1856) (aligned : bs.val.length%16=0)
    (shape : before.val.length=2*bs.val.length)
    (trace : NativeTrace bs.val before.val (bs.val.length/16) after.val) :
    LPt_External.compact.expand_values bs before = ok (.Ok (),after) :=
  LPt_LPl.Expand.native_result bs before after bound aligned shape
    (to_inherited _ _ _ _ trace)

theorem unique (bs initial a b : List U8) (n : Nat)
    (done : 32*n=initial.length)
    (left : NativeTrace bs initial n a) (right : NativeTrace bs initial n b) : a=b :=
  LPt_LPl.Expand.unique bs initial a b n done
    (to_inherited _ _ _ _ left) (to_inherited _ _ _ _ right)

theorem length_error (bs before : Slice U8) (bound : bs.val.length≤1856)
    (bad : bs.val.length%16≠0 ∨ before.val.length≠2*bs.val.length) :
    LPt_External.compact.expand_values bs before = ok (.Err .Length,before) :=
  LPt_LPl.Expand.length_error bs before bound bad

#print axioms to_inherited
#print axioms of_inherited
#print axioms total
#print axioms native_result
#print axioms unique
#print axioms length_error
end LPt_LPn.Expand
