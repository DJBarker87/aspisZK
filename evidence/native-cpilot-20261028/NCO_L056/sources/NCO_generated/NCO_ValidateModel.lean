import NCO_OuterRun
import NCO_GoodModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NCO_ValidateModel
attribute [local instance] Classical.propDecidable

def error : NCO_ParserRef.RefError → LPl_Kit_Release.r1_wire.Error
  | .InvalidRow => .InvalidRow
  | .Length row => .Length row
  | .Tag row => .Tag row
  | .NonCanonical row value => .NonCanonical row value

def result {α : Type} : core.result.Result α NCO_ParserRef.RefError →
    core.result.Result α LPl_Kit_Release.r1_wire.Error
  | .Ok a => .Ok a
  | .Err e => .Err (error e)

theorem bad (payload : Slice U8) (i : Nat) :
    NCO_OuterRun.bad payload i =
      !LPl_Kit_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32) := by
  cases h : LPl_Kit_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32) with
  | false =>
    have no : ¬NCO_Inner.GoodFrom payload i 0 := by
      intro yes
      have t := (NCO_GoodModel.row payload i).mp yes
      rw [h] at t
      contradiction
    simp [NCO_OuterRun.bad,no,h]
  | true =>
    have yes := (NCO_GoodModel.row payload i).mpr h
    simp [NCO_OuterRun.bad,yes,h]

theorem reference (row : U8) (payload : Slice U8) (cap : payload.val.length ≤ 3712) :
    (do let r ← NCO_ParserRef.validate_ref row payload; ok (result r)) =
      _root_.r1_wire.validate_record_fields row payload := by
  obtain ⟨final,pending,call,outcome⟩ := NCO_OuterRun.run payload 0#usize cap (by scalar_tac)
  have zero : (0#usize).val=0 := by scalar_tac
  rw [zero] at outcome
  unfold NCO_ParserRef.validate_ref
  rw [call]
  simp only [bind_tc_ok]
  unfold NCO_OuterRun.Outcome at outcome
  rw [NCO_Search.from_zero] at outcome
  have sameBad : NCO_OuterRun.bad payload = fun i =>
      !LPl_Kit_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32) := by
    funext i
    exact bad payload i
  rw [sameBad] at outcome
  unfold _root_.r1_wire.validate_record_fields
  cases found : (List.range (payload.val.length/32)).find? (fun i =>
      !LPl_Kit_Bytes.validChunk 8 true ((payload.val.drop (32*i)).take 32)) with
  | none =>
    rw [found] at outcome
    rcases outcome with ⟨_,rfl⟩
    rfl
  | some k =>
    rw [found] at outcome
    rcases outcome with ⟨value,rfl⟩
    have member := List.mem_of_find?_eq_some found
    have bound : k < payload.val.length/32 := List.mem_range.mp member
    have small : k < 116 := by omega
    have representable : k ≤ UScalar.cMax .Usize := by scalar_tac
    dsimp only
    rw [dif_pos representable]
    have same : final = UScalar.ofNat k representable := by
      apply UScalar.eq_of_val_eq
      simpa using value
    simp only [bind_tc_ok,result,error,same]

#print axioms bad
#print axioms reference
end NCO_ValidateModel
