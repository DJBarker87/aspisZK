import BEk_Projection
import BEj_ReifiedBatch
import Port4B_BatchJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEk_LocalAssociation
open Aeneas Aeneas.Std Result SdkC_Source

/-- Conditional, source-operational association at the exact BEj input arrays
and ordinal, permitting distinct native/common state types. The native
physical-to-source step extraction is still missing; this is NOT the requested
unconditional physical BothSlots instance. Port4B's scratch induction is
imported unchanged, not repeated or hidden in an admission predicate. -/
theorem of_step_projection {N S : Type} (project : N → S)
    (nativeCall : Parts → N → Result Digest × N)
    (sourceCall : Parts → S → Result Digest × S)
    (step : ∀ parts state, (nativeCall parts state).1 = (sourceCall parts (project state)).1 ∧
      project (nativeCall parts state).2 = (sourceCall parts (project state)).2)
    (hashv : Parts → Result Digest) :
    BEh_Scope.BothSlots
      (fun (input : BEj_ReifiedBatch.Input × N) (_ : Fin 2) (state : S) => project input.2 = state)
      (fun input slot state before => BEk_Projection.outcome project
        (BEf_Carrier.run nativeCall (BEj_ReifiedBatch.nativeCode hashv input.1 slot) input.2 before))
      (fun input slot state before =>
        BEf_Carrier.run sourceCall (BEj_ReifiedBatch.sourceCode hashv input.1 slot) state before) := by
  intro input slot state before admitted
  dsimp only at admitted ⊢
  rw [←admitted]
  dsimp only
  rw [BEj_ReifiedBatch.programs,BEk_Projection.run project nativeCall sourceCall step]
  exact BEh_Scope.reflexive _

#print axioms of_step_projection
end AspisR1.BEk_LocalAssociation
end
