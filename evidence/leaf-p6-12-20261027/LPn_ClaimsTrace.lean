import LPn_ClaimsFold
import LPn_DecodeBounds
open Aeneas Aeneas.Std Result LPl_Kit_Release
set_option autoImplicit false
namespace LPn.Claims
open LPn.ClaimsModel

/-- Each call is the CLOSED decode leaf on this SAME record, not an
    independently chosen decoded row or final Claims result. -/
inductive Step (r : r1_wire.ValidatedRecord) : State → Nat → State → Prop where
  | stopped (e : r1_wire.Error) (point : Nat) : Step r (.Err e) point (.Err e)
  | reject (rows : List Row) (point : Nat) (e : r1_wire.Error)
      (call : r1_wire.ValidatedRecord.decode_k 29#usize r (LPn_Kit_usize (point*29)) = ok (.Err e)) :
      Step r (.Ok rows) point (.Err e)
  | write (rows : List Row) (point : Nat) (row : Row)
      (call : r1_wire.ValidatedRecord.decode_k 29#usize r (LPn_Kit_usize (point*29)) = ok (.Ok row)) :
      Step r (.Ok rows) point (.Ok (rows++[row]))

theorem step_eq (r : r1_wire.ValidatedRecord) (before after : State) (point : Nat)
    (h : Step r before point after) : LPn.ClaimsModel.step r before point = ok after := by
  cases h with
  | stopped => rfl
  | reject rows point e call => simp only [LPn.ClaimsModel.step,call,bind_tc_ok]
  | write rows point row call => simp only [LPn.ClaimsModel.step,call,bind_tc_ok]

inductive Trace (r : r1_wire.ValidatedRecord) : Nat → State → Prop where
  | init : Trace r 0 (.Ok [])
  | next (n : Nat) (before after : State) (rest : Trace r n before)
      (step : Step r before n after) : Trace r (n+1) after

theorem stages_eq (r : r1_wire.ValidatedRecord) (n : Nat) (after : State)
    (trace : Trace r n after) :
    LPn.stagesM (LPn.ClaimsModel.step r) (.Ok []) n = ok after := by
  induction trace with
  | init => rfl
  | next n before after rest step ih =>
    simp only [LPn.stagesM,ih,bind_tc_ok]
    exact step_eq r before after n step

theorem success_length (r : r1_wire.ValidatedRecord) (n : Nat) (rows : List Row)
    (trace : Trace r n (.Ok rows)) : rows.length=n := by
  generalize eq : core.result.Result.Ok rows = state at trace
  induction trace generalizing rows with
  | init => cases eq;rfl
  | next n before after rest step ih =>
    cases step with
    | stopped => cases eq
    | reject => cases eq
    | write prior point row call =>
      cases eq
      have size := ih prior rfl
      simp only [List.length_append,List.length_singleton,size]

theorem from_record (r : r1_wire.ValidatedRecord) (after : State)
    (trace : Trace r 3 after) :
    LPn.ClaimsModel.fromRecord r = LPn.ClaimsModel.finish after := by
  unfold LPn.ClaimsModel.fromRecord LPn.ClaimsModel.loop
  rw [stages_eq r 3 after trace]
  rfl

theorem prefix_result (p : r1_wire.Prefix) (framed : Slice U8) (after : State)
    (read : Array.index_usize p.records 25#usize = ok framed)
    (trace : Trace ⟨25#u8,framed⟩ 3 after) :
    r1_semantic.claims p = LPn.ClaimsModel.finish after := by
  rw [LPn.ClaimsModel.leaf_eq_loop,read]
  simp only [bind_tc_ok]
  exact from_record _ after trace

/-- Preserve the allocator's actual return partition explicitly. Allocation
    rejection has no decoder/query/write suffix. No new allocator law. -/
def owned (reserved : Bool) (p : r1_wire.Prefix) :
    Result (core.result.Result (Array Row 3#usize) r1_wire.Error) :=
  if reserved then r1_semantic.claims p else ok (.Err .Allocation)

theorem allocated_result (reserved : Bool) (p : r1_wire.Prefix)
    (framed : Slice U8) (after : State)
    (read : Array.index_usize p.records 25#usize = ok framed)
    (trace : Trace ⟨25#u8,framed⟩ 3 after) :
    owned reserved p = if reserved then LPn.ClaimsModel.finish after else ok (.Err .Allocation) := by
  unfold owned
  rw [prefix_result p framed after read trace]

theorem accepted_to_cohort (reserved : Bool) (p : r1_wire.Prefix)
    (out : Array Row 3#usize) (accepted : owned reserved p = ok (.Ok out)) :
    reserved=true ∧ r1_semantic.claims p = ok (.Ok out) := by
  cases reserved <;> simp_all [owned]

#print axioms step_eq
#print axioms stages_eq
#print axioms success_length
#print axioms from_record
#print axioms prefix_result
#print axioms allocated_result
#print axioms accepted_to_cohort
end LPn.Claims
