import CuSavingsGammaPrefixData
set_option autoImplicit false
namespace AspisR1.CuSavingsGammaCandidate1
open Aeneas Aeneas.Std Result AspisR1CuGamma
open CuSavingsGammaTable CuSavingsGammaSourceBinding CuSavingsGammaPrefixData

/-- Execution of the exact, common complete source tail with its free values.
There is one interpreter, not separate old/new claims or an equivalence law.
Every tail operation, error and divergence is left arbitrary. -/
class SourceTail where
  run : {H : Type} → aspis_core.Digest32 H → r1_semantic.Verified H → Slice U8 →
    E → E → List String → Table → Result (core.result.Result E Err)

/-- Source-directed binding of the two claim boundaries. The remaining fields
are precisely the existing unchanged source interpretations. -/
def sourceBoundaries (common : Boundaries) (tail : SourceTail) : Boundaries :=
  { common with
    oldClaim := fun D sem y1 inactive gamma kappa =>
      execute (tail.run D sem y1 inactive kappa) (common.powers 29#usize)
        gamma (Array.repeat 29#usize aspis_core.field.WideExact.ZERO) parentBlock
    newClaim := fun D sem y1 inactive g kappa =>
      execute (tail.run D sem y1 inactive kappa) (common.powers 29#usize)
        aspis_core.field.WideExact.ZERO g candidateBlock }

/-- The missing local contract follows from the checked source prefix and
identical tail, without a claim-equivalence or tail-success premise. -/
theorem source_claim_factor (common : Boundaries) (tail : SourceTail)
    {H : Type} (D : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (inactive gamma kappa : E) :
    letI : Boundaries := sourceBoundaries common tail
    gamma_old.prepared_claim D sem y1 inactive gamma kappa =
      (do let g ← weights.powers 29#usize gamma
          gamma_new.prepared_claim D sem y1 inactive g kappa) := by
  change execute (tail.run D sem y1 inactive kappa) (common.powers 29#usize)
    gamma (Array.repeat 29#usize aspis_core.field.WideExact.ZERO) parentBlock = _
  rw [prefix_identity]
  rfl

/-- Complete existing emitted tx1 callers composed with the source binding
certificate. No local claim-factor equation is supplied by the caller. -/
theorem source_tx1_equivalence (common : Boundaries) (tail : SourceTail)
    [CallerBoundaries] {H : Type} (D : aspis_core.Digest32 H)
    (publicValue : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) :
    letI : Boundaries := sourceBoundaries common tail
    gamma_old.tx1 D publicValue publicBytes proof k hash obs =
      gamma_new.tx1 D publicValue publicBytes proof k hash obs := by
  letI : Boundaries := sourceBoundaries common tail
  exact CuSavingsGammaTx1.source_eq_of_claim_factor D publicValue publicBytes proof k hash obs
    (fun sem v gamma kappa => source_claim_factor common tail D sem v.y1 v.inactive gamma kappa)

#print axioms SourceTail
#print axioms source_claim_factor
#print axioms source_tx1_equivalence
end AspisR1.CuSavingsGammaCandidate1
