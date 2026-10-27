import RPu_FIr_SourceChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_SourceLast
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun
open FIr_SourceChain (K W)

theorem last_value {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (alpha : Array aspis_core.field.QM31 10#usize) (same : entries.map RoundEvidence.q=alpha.val) :
    (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values 9)).eval
      (algebraMap K W (DecodeMain (alpha.val[9]'(by have len := alpha.property;change alpha.val.length=10 at len;omega))))=
      algebraMap K W (DecodeMain final.1) := by
  have chain := annotatedRun_to_chain D pre _ _ _ entries run
  have last := FIr_Chain.last_value chain 9 (by simp only [List.length_map,FIr_EntryIndex.length run])
  simp only [List.getElem_map,pairOf,challengeOf] at last
  have mapped := congrArg (algebraMap K W) last
  rw [← FIr_SourceChain.polynomial run values full 9]
  erw [← FIr_EntryIndex.challenge run alpha same 9,Polynomial.eval_map_apply]
  exact mapped

#print axioms last_value
end AspisR1.FIr_SourceLast
end
