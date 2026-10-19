import ActualFinishFieldWitnesses
import RawActualSemanticRoundCanonicality
import SemanticRoundAlphaSelectedCanonical

/-! Derive source alpha/tail canonicality from successful finish execution
with the actual decoder, retaining terminal and claim-producing boundaries. -/
set_option autoImplicit false
namespace AspisR1PublicPreparation.ActualFinishInputCanonicality
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawSemanticFieldOwnerAdapter
open AspisR1PublicPreparation.ActualFinishConcreteArithmeticBoundary
open AspisR1PublicPreparation.ActualMainMaskPopulatedBridge

 theorem finish_alpha_and_tails_canonical
    (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges)
    (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (hfinish : FinishModel.finish RawActualSemanticRoundCanonicality.actualRoundBoundaries
      B D pub pre before challenges obs = .ok (.Ok out)) :
    CanonicalArray out.alpha ∧ CanonicalArray out.extra ∧ CanonicalArray out.before_z1 := by
  obtain ⟨running,afterRounds,record25,record26,z0,t26,z1,t27,
      hrounds,hchallenges,hstate,htranscript,hclaims,hrecord25,
      hextra,hcircle25,hrecord26,hbeforeZ1,hcircle26,hz⟩ :=
    FinishCalls.finish_success RawActualSemanticRoundCanonicality.actualRoundBoundaries
      B D pub pre before challenges obs out hfinish
  have halpha := SemanticRoundAlphaSelectedCanonical.verifier_round_alpha_canonical
    RawActualSemanticRoundCanonicality.actualRoundBoundaries D pre before afterRounds
    running out.alpha hrounds
  have hextra' : RawActualDecodeKMainAdapter.decodeMain 29#usize record25 87#usize =
      .ok (.Ok out.extra) := hextra
  have hbeforeZ1' : RawActualDecodeKMainAdapter.decodeMain 29#usize record26 0#usize =
      .ok (.Ok out.before_z1) := hbeforeZ1
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simpa only [SemanticRoundAlphaSelectedCanonical.ToSelected,
      SemanticCallSelectedCanonical.toSelected, mainToProbe] using halpha i
  · exact RawActualDecodeKMainAdapter.decodeMain_success_canonical
      29#usize record25 87#usize out.extra hextra'
  · exact RawActualDecodeKMainAdapter.decodeMain_success_canonical
      29#usize record26 0#usize out.before_z1 hbeforeZ1'

 theorem canonical_index_of_success {n : Usize} (xs : Array MainQM n)
    (hcanonical : CanonicalArray xs) (index : Usize) (hi : index.val < n.val)
    (value : MainQM) (hread : Array.index_usize xs index = .ok value) :
    Canonical (mainToProbe value) := by
  have heq := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok xs index hi
  have hv : xs.val[index.val]'(by simpa [xs.property] using hi) = value :=
    Result.ok.inj (heq.symm.trans hread)
  rw [← hv]
  exact hcanonical ⟨index.val,hi⟩

#print axioms finish_alpha_and_tails_canonical
#print axioms canonical_index_of_success
end AspisR1PublicPreparation.ActualFinishInputCanonicality
