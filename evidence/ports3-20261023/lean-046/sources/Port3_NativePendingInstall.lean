import Port3_NativePendingLoop
import Port3_WriterShape

/-! Install the CURRENT emitted while-loop constructor, with the existing
fallible TrustedStd heap interpretation. Equality to the row reference is
proved on length64; no equality/rejection claim concerns other lengths. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port3_NativePendingInstall
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativePendingBody
abbrev K := aspis_core.field.QM31

def heap (reserved : Bool) (n : Usize) (value : Row) :
    Result (core.result.Result (alloc.vec.Vec Row) Unit) := do
  let out ← OraclePortStdAllocation.filled n value reserved
  match out with
  | .error _ => ok (.Err ())
  | .ok raw => ok (.Ok raw)

theorem heap_exact (reserved : Bool) (n : Usize) (value : Row) :
    heap reserved n value = if reserved then
      ok (.Ok ⟨List.replicate n.val value,by simp; scalar_tac⟩) else ok (.Err ()) := by
  cases reserved <;> simp [heap,OraclePortStdAllocation.filled_exact,OraclePortStdAllocation.filledSpec]

def source (reserved : Bool) (weights : Slice K) :=
  Port3_QueryInstall.result (extracted (heap reserved) weights)

def initialRaw (weights : Slice K) : alloc.vec.Vec Row :=
  ⟨List.replicate weights.val.length (Array.repeat 4#usize 0#u64),by simpa using weights.property⟩

theorem emitted_exact (reserved : Bool) (weights : Slice K) (size : weights.val.length=64) :
    extracted (heap reserved) weights = if reserved then
      ok (.Ok ⟨Port3_PendingInstall.raw weights,0#usize⟩) else ok (.Err .Allocation) := by
  cases reserved with
  | false =>
    simp only [extracted,heap_exact,if_false,bind_tc_ok]
    rfl
  | true =>
    obtain ⟨out,run,contents⟩ := Port3_NativePendingLoop.run_total weights (initialRaw weights)
      0#usize 64 size (by simp [initialRaw,size]) (by decide)
      (by intro j hj; change j<0 at hj; omega)
    have same : out=Port3_PendingInstall.raw weights := Subtype.ext contents
    simp only [extracted,heap_exact,if_true,bind_tc_ok]
    change (do let raw ← Port3_NativePendingBody.run weights (initialRaw weights) 0#usize
               ok (.Ok ⟨raw,0#usize⟩)) = _
    rw [run,bind_tc_ok,same]

theorem reference_eq (reserved : Bool) (weights : Slice K) (size : weights.val.length=64) :
    source reserved weights=Port3_PendingInstall.pending reserved weights := by
  rw [source,emitted_exact reserved weights size,Port3_PendingInstall.pending_exact]
  cases reserved <;> rfl

/-- All fields of the SAME successful native constructor output. -/
theorem accepted_fields (reserved : Bool) (weights : Slice K) (state : verifier.BatchedWeights)
    (size : weights.val.length=64) (success : source reserved weights=ok (.Ok state)) :
    reserved=true ∧ state.raw.val=weights.val.map Port3_PendingInstall.row ∧ state.terms=0#usize ∧
      state.raw.val.length=64 := by
  rw [reference_eq reserved weights size] at success
  have fields := Port3_PendingInstall.accepted_fields reserved weights state success
  exact ⟨fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.trans size⟩

def installed (base : VTop_Stages.Ops) (reserved : Bool) (aops : AccumulateOps) (qops : QueryOps) : VTop_Stages.Ops :=
  {Port3_WriterShape.installed base reserved aops qops with op10 := source reserved}

#print axioms heap_exact
#print axioms emitted_exact
#print axioms reference_eq
#print axioms accepted_fields
end AspisR1.Port3_NativePendingInstall
end
