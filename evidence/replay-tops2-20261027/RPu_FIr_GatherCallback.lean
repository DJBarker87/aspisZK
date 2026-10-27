import RPu_FIr_BuilderCanonical
import RPu_FIq_Native03
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_GatherCallback
open Aeneas Aeneas.Std Result
open FIr_NativeArithmetic (NQ)
open FIr_NativeValue (Canon)
abbrev Claims := Array (Array NQ 29#usize) 3#usize
abbrev call := FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut

def CanonClaims (claims : Claims) : Prop := ∀ row∈claims.val,∀ x∈row.val,Canon x

theorem selected (claims : Claims) (i : Usize) (out : NQ) (after : Claims)
    (all : CanonClaims claims) (run : call claims i=ok (out,after)) :
    Canon out ∧ after=claims := by
  unfold call FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut at run
  obtain ⟨rowIndex,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨column,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨row,readRow,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨q,readCell,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Prod.mk.inj (Result.ok.inj run)
  obtain ⟨rfl,rfl⟩ := same
  exact ⟨all row (FIr_ArrayRead.member claims rowIndex row readRow) q
    (FIr_ArrayRead.member row column q readCell),rfl⟩

#print axioms selected
end AspisR1.FIr_GatherCallback
end
