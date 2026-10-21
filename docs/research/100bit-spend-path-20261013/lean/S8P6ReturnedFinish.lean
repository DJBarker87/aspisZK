import S8JoinRawCongruence
import OraclePortFrozen2Decision

/-! Complete mutable finish at the *returned* frozen2 accumulator, rather
than an independently reconstructed run22. The dot below is the field
reference: adoption of finish_query_dot/finish_relation is still open. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S8P6ReturnedFinish
open Aeneas Aeneas.Std Result
open S8OwnedP6Finish S8OwnedP6ValueModel S8JoinFinishField
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortStoredDecisionDraftC4 OraclePortFrozen2
open RecordedBinaryExperimentBin (SourceInputs)
open RawCutTranscriptRun (ErasedPrefix)
open scoped BigOperators
attribute [local instance] Classical.propDecidable
abbrev FinishSlice := S8Kani2MutableExtraction.batched_weights.FinishSlice
abbrev Acc := QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E

/-- Only the reached storage representation is a caller obligation. No
callee success, final dot equality or whole-function correspondence occurs. -/
structure Caller (raw : Raw) (destination : Weights) (a : Acc) : Prop where
  size : destination.length=64
  lengths : destination.length≤raw.length
  fields : ∀ (l : Fin 64) row, raw.val[l.val]?=some row → rawValue row=a.weights l

def fieldAt (out : FinishSlice) (l : Fin 64) : OraclePortCheckpointAbiC5.K :=
  ((out.val[l.val]?).map mutableField).getD 0

/-- Exact returned list, including arbitrary old destination cells and any
unused raw suffix. There is no term-counter/phase/raw-value bound. -/
theorem mutable_certificate (raw : Raw) (destination : Weights) (terms : Usize)
    (a : Acc) (caller : Caller raw destination a) :
    ∃ out : FinishSlice,
      S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
        (⟨raw,terms⟩ : S8Kani2MutableValue.F.BW)
        (S8Kani2FinishReferenceJoin.toSlice destination)=ok out ∧
      out.val.map mutableField=List.ofFn a.weights := by
  obtain ⟨out,run,fields⟩ := mutable_field raw destination terms caller.lengths
  refine ⟨out,run,fields.trans ?_⟩
  apply List.ext_getElem
  · simp only [List.length_map,List.length_take,List.length_ofFn]
    change min destination.length raw.length=64
    rw [Nat.min_eq_left caller.lengths,caller.size]
  · intro j hj hk
    have bound : j<64 := by simpa only [List.length_ofFn] using hk
    have read : j<raw.val.length := by
      have len : destination.val.length≤raw.val.length := caller.lengths
      have size : destination.val.length=64 := caller.size
      omega
    simp only [List.getElem_map,List.getElem_take,List.getElem_ofFn]
    exact caller.fields ⟨j,bound⟩ _ (List.getElem?_eq_getElem read)

/-- The source-shaped traversal is real; the final dot is explicitly the
field-reference consumer, not an assumed EbyKDot source certificate. -/
def finish (raw : Raw) (destination : Weights) (terms : Usize)
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (a : Acc) : Result Bool := do
  let out ← S8Kani2MutableExtraction.batched_weights.BatchedWeights.finish
    (⟨raw,terms⟩ : S8Kani2MutableValue.F.BW)
    (S8Kani2FinishReferenceJoin.toSlice destination)
  ok (D0TypedChecks.verify (typedRows p q tr) i &&
    decide ((∑ l : Fin 64, i.data.f l * LiteralOpeningView.eK (fieldAt out l))=a.rhs))

/-- Whole mutable finish and field check, on both true and false arithmetic
results, at any accumulator returned by the checkpoint. -/
theorem finish_certificate (raw : Raw) (destination : Weights) (terms : Usize)
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (a : Acc) (caller : Caller raw destination a) :
    finish raw destination terms p q tr i a=ok (OraclePortFrozen2.finish p q tr i a) := by
  obtain ⟨out,run,fields⟩ := mutable_certificate raw destination terms a caller
  have cells (l : Fin 64) : fieldAt out l=a.weights l := by
    have selected :=  congrArg (fun xs => xs[l.val]?) fields
    simpa only [List.getElem?_map,List.getElem?_ofFn,dif_pos l.isLt,fieldAt,
      Option.getD_some] using congrArg (fun v => v.getD 0) selected
  simp only [finish,run,bind_tc_ok,cells,OraclePortFrozen2.finish]

def stage2 (raw : Raw) (destination : Weights) (terms : Usize)
    (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (a : Acc) : Program Bytes State Bool :=
  bind (batch p q batch1) fun ok =>
    match finish raw destination terms p q tr i a with
    | .ok b => .done (ok && b)
    | _ => .done false

/-- All batch1 reads and answers and the exact returned-state dependency.
This is a finish-port stage join, not a complete S8 source-cone claim. -/
theorem stage_observation (H : Bytes → State) (raw : Raw) (destination : Weights)
    (terms : Usize) (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (a : Acc) (caller : Caller raw destination a) :
    eval H (stage2 raw destination terms p q tr i a)=
      eval H (OraclePortFrozen2.stage2 p q tr i a) := by
  simp only [stage2,finish_certificate raw destination terms p q tr i a caller,
    OraclePortFrozen2.stage2]

#print axioms mutable_certificate
#print axioms finish_certificate
#print axioms stage_observation
end AspisR1.S8P6ReturnedFinish
end
