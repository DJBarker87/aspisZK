import SemanticPackedOuterClosed
import TerminalSemanticPublicDigestCanonical

set_option autoImplicit false
namespace AspisR1.SemanticPackedSixFamiliesActualPreparation
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.SemanticPackedSixFamilies
open AspisR1.ExtractedMaskQmPackBase4Semantic
open AspisR1.PreweightedClosureSuccess
open AspisR1.PreweightedGroupUpdate
open AspisR1.PreweightedLoopModel
open AspisR1.ValueFamilyFieldTransport
open AspisR1TerminalDigestBindingCandidate.SemanticPublicPreparationCopy
open AspisR1TerminalDigestBindingCandidate.SemanticPublicDigestCanonical

/-- The retained actual preparation success supplies all digest-word bounds
needed by the six-family semantic caller. Only point/opening canonicality and the boxed-selector premise remain explicit. -/
theorem actual_semantic_packed_of_preparation
    (point : Array QM 10#usize) (selectors : Selectors)
    (s : AspisR1TerminalDecoder.PublicBinding.Statement)
    (openings : Openings)
    (hpoint : CanonicalArray point)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectors)
    (hz : CanonicalArray openings.z) (hsucc : CanonicalArray openings.succ_z)
    (hxor : CanonicalArray openings.xor12_z)
    {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (hash : H) (c1 : Array U8 32#usize)
    (outTranscript : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (hprep : AspisR1PublicPreparation.r1_semantic.public_transcript D
      (AspisR1PublicPreparation.PreparationBinding.preparationPublic s)
      hash c1 = Result.ok (.Ok outTranscript)) :
    ∃ out,
      AspisR1SemanticPackedBoundedCandidate.pool_v1.pair_forest_semantic_terminal.semantic_packed
        (copyFromStatement s) openings selectors = .ok out ∧ CanonicalArray out ∧
      ∀ j : Fin 24, f (decoded out j) =
        R0P.pack4 PackB (fun k => R0P.SemSource.scalarLaneAt
          (publicWide (copyFromStatement s))
          (mapOpenings f (exactOpenings openings))
          (fun i => f (pointSelector point i)) (4*j.val+k.val)) := by
  have hcanon := actual_preparation_digest_inputs_canonical D s hash c1 outTranscript hprep
  rcases hcanon with ⟨ha, hn, hc, hr, hsnapshot, hroot, hfrontier, hasset, hamountOpt⟩
  have hamount : (AspisR1.ScalarSuffixExecution.amountValue (copyFromStatement s)).val <
      AspisR1.TerminalLiftM31Exact.P := by
    cases hwithdraw : (copyFromStatement s).withdrawal_amount with
    | none =>
        norm_num [AspisR1.ScalarSuffixExecution.amountValue, hwithdraw,
          AspisR1.TerminalLiftM31Exact.P, AspisR1.ExtractedMaskTowerAdd.P]
    | some a =>
        have h := hamountOpt a hwithdraw
        simpa [AspisR1.ScalarSuffixExecution.amountValue, hwithdraw,
          AspisR1.TerminalLiftM31Exact.P] using h
  have hasset' : (copyFromStatement s).asset_id.val < AspisR1.TerminalLiftM31Exact.P := by
    simpa [AspisR1.TerminalLiftM31Exact.P] using hasset
  exact AspisR1.SemanticPackedOuterClosed.actual_semantic_packed
    point selectors (copyFromStatement s) openings
    hpoint hbox hz hsucc hxor ha hn hc hr hsnapshot hroot hfrontier hasset' hamount

#print axioms actual_semantic_packed_of_preparation
end
end AspisR1.SemanticPackedSixFamiliesActualPreparation
