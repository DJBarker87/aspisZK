import S1DecodedSampledValueTotalV1
import ExtractedSemanticRoundsCheckedTrace
import SemanticRoundAlphaSelectedCanonical
set_option autoImplicit false
namespace AspisS1AcceptedRoundsNumeric
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren
open SemanticRoundsCheckedTrace

/-- Same actual checked step and both arithmetic return ranges. The round
bound is derived from the fixed source schedule in the enclosing theorem. -/
def NumericStep {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (before after : Outcome H) (round : Usize) (row : U8) : Prop :=
  CheckedStep children D pre before after round row ∧ round.val < 10 ∧
    Canonical before.1 ∧ Canonical after.1

/-- Execution order and the original decoded/sampled/check witnesses remain
in each CheckedStep. This is an output predicate, never a caller premise. -/
inductive NumericRun {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix) :
    List (Usize × U8) → Outcome H → Outcome H → Prop
  | nil (out : Outcome H) : NumericRun D pre [] out out
  | cons {round : Usize} {row : U8} {rest : List (Usize × U8)}
      {before mid after : Outcome H}
      (step : NumericStep D pre before mid round row)
      (tail : NumericRun D pre rest mid after) :
      NumericRun D pre ((round,row)::rest) before after

theorem checked_step_numeric {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (before after : Outcome H) (round : Usize) (row : U8)
    (checked : CheckedStep children D pre before after round row)
    (hr : round.val < 10) : NumericStep D pre before after round row := by
  obtain ⟨record,p,b,q,recordCall,decoded,boundary,comparison,beforeEq,sample,updated,value⟩ := checked
  obtain ⟨boundaryOut,boundaryCall,boundaryCanon⟩ := decoded_boundary_total record 0#usize p decoded
  have boundaryEq : boundaryOut = b := Result.ok.inj (boundaryCall.symm.trans boundary)
  have beforeCanon : Canonical before.1 := by
    simpa only [boundaryEq,beforeEq] using boundaryCanon
  have qCanon := sampled_canonical D before.2.2 after.2.2 record q sample
  have selected : Canonical (after.2.1.val[round.val]'(by simpa [after.2.1.property] using hr)) := by
    rw [updated]
    simpa [Array.set] using qCanon
  obtain ⟨valueOut,valueCall,valueCanon⟩ := decoded_value_total_selected
    record 0#usize p after.2.1 round decoded hr selected
  have valueEq : valueOut = after.1 := Result.ok.inj (valueCall.symm.trans value)
  exact ⟨⟨record,p,b,q,recordCall,decoded,boundary,comparison,beforeEq,sample,updated,value⟩,
    hr,beforeCanon,by simpa only [valueEq] using valueCanon⟩

theorem checked_run_numeric {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (steps : List (Usize × U8)) (before after : Outcome H)
    (run : CheckedRun children D pre steps before after)
    (bounds : ∀ step ∈ steps, step.1.val < 10) : NumericRun D pre steps before after := by
  induction run with
  | nil out => exact NumericRun.nil out
  | @cons round row rest before mid after step tail ih =>
    exact NumericRun.cons (checked_step_numeric D pre before mid round row step
      (bounds (round,row) (by simp))) (ih (fun s hs => bounds s (by simp [hs])))

theorem numeric_run_last {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (steps : List (Usize × U8)) (before after : Outcome H)
    (run : NumericRun D pre steps before after) (nonempty : steps ≠ []) : Canonical after.1 := by
  induction run with
  | nil out => exact False.elim (nonempty rfl)
  | @cons round row rest before mid after step tail ih =>
    by_cases empty : rest = []
    · subst rest
      cases tail
      exact step.2.2.2
    · exact ih empty

/-- One complete accepted source-model rounds execution supplies all ten
arithmetic domains. There are no separate decode/sample/update successes,
coefficient/alpha canonicality premises or independently successful arithmetic
children. This is ACCEPTED-ONLY for the parent, with TOTAL reached arithmetic
children reused above; it is not arbitrary-input native/SDK totality. -/
theorem accepted_rounds_numeric {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (self after : r1_wire.SemanticTranscript H)
    (running : MainQM) (alpha : Array MainQM 10#usize)
    (accepted : RoundModel.rounds children D pre self = ok (.Ok (running,alpha,after))) :
    ∃ record initialArray initial,
      r1_wire.Prefix.validated_record pre 14#u8 = ok (.Ok record) ∧
      children.decode 1#usize record 0#usize = ok (.Ok initialArray) ∧
      Array.index_usize initialArray 0#usize = ok initial ∧
      NumericRun D pre schedule
        (initial,Array.repeat 10#usize aspis_core.field.QM31.ZERO,self) (running,alpha,after) ∧ Canonical running ∧
      (∀ i : Fin 10, Canonical (alpha.val[i.val]'(by simpa [alpha.property] using i.isLt))) := by
  obtain ⟨record,initialArray,initial,recordCall,decoded,indexed,run⟩ :=
    rounds_checked_success children D pre self after running alpha accepted
  have bounds : ∀ step ∈ schedule, step.1.val < 10 := by
    intro step member
    simp only [schedule,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with h|h|h|h|h|h|h|h|h|h <;> subst step <;> decide
  have numeric := checked_run_numeric D pre schedule _ _ run bounds
  refine ⟨record,initialArray,initial,recordCall,decoded,indexed,numeric,
    numeric_run_last D pre schedule _ _ numeric (by simp [schedule]),?_⟩
  intro i
  exact SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
      children D pre self after running alpha accepted i

#print axioms checked_step_numeric
#print axioms checked_run_numeric
#print axioms numeric_run_last
#print axioms accepted_rounds_numeric
end AspisS1AcceptedRoundsNumeric
