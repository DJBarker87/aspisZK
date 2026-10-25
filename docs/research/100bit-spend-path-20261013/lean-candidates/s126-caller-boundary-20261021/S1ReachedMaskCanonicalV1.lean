import S1ReachedMaskInputsV1
import S1SourceMaskTotalV1
set_option autoImplicit false
namespace AspisS1ReachedMaskCanonical
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren

/-- The actual selectors, row0column27 and mask return of the same source
semantic witness; the returned value itself has all four canonical words. -/
def ReachedCanonicalMask {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) : Prop :=
  ∃ (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
    (row0 : Array MainQM 29#usize) (g value : MainQM),
    AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first ∧
    AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second ∧
    Array.index_usize sem.claims 0#usize=ok row0 ∧
    Array.index_usize row0 27#usize=ok g ∧
    AspisS1SourceMaskOps.mask first second g sem.alpha=ok value ∧
    AspisS1SourceMaskOps.Canonical value

/-- The actual normally returned mask value is the TOTAL theorem's value by
functional source equality. No independent value or mask-output range is an
input premise. Its reached input ranges are discharged by the SDK parent. -/
theorem canonical_of_reached_inputs {H : Type} (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H)
    (reached : AspisS1ReachedMaskInputs.ReachedMaskInputRanges D sem) :
    ReachedCanonicalMask D sem := by
  obtain ⟨first,second,row0,g,value,hfirst,hsecond,hrow,hg,hmask,cf,cs,cg,ca⟩ := reached
  obtain ⟨actual,called,canonical⟩ := AspisS1SourceMaskOps.mask_total
    first second g sem.alpha cf cs cg ca
  have same : actual=value := Result.ok.inj (called.symm.trans hmask)
  subst actual
  exact ⟨first,second,row0,g,value,hfirst,hsecond,hrow,hg,hmask,canonical⟩

#print axioms canonical_of_reached_inputs
end AspisS1ReachedMaskCanonical
