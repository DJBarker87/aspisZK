import FIr_EntryIndex
import FIr_Chain
import FIr_ChallengeValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_SourceChain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun
abbrev K := ExtractedMaskQM31Exact.QM31Exact
abbrev W := AspisWideTower.WideExact

theorem polynomial {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre) (j : Fin 10) :
    (polynomialOf (entries[j.val]'(by rw [FIr_EntryIndex.length run];exact j.isLt)).coefficients).map
      (algebraMap K W)=SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values j) := by
  let entry := entries[j.val]'(by rw [FIr_EntryIndex.length run];exact j.isLt)
  have mem : entry ∈ entries := List.getElem_mem _
  have same := FIq_TypedPolynomials.same_entry (⟨[],by simp⟩ : Slice U8) pre values full
    D initial final entries run entry mem
  have idx : (⟨entry.round.val,RawActualAnnotatedTypedRows.entry_schedule_round_lt run entry mem⟩ : Fin 10)=j :=
    Fin.ext (FIr_EntryIndex.round run j)
  rw [idx] at same
  exact same

theorem adjacent {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre)
    (alpha : Array aspis_core.field.QM31 10#usize) (same : entries.map RoundEvidence.q=alpha.val)
    (j : Fin 9) :
    (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values j.succ)).eval 0+
      (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values j.succ)).eval 1=
    (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values j.castSucc)).eval
      (algebraMap K W (DecodeMain (alpha.val[j.val]'(by have len := alpha.property;change alpha.val.length=10 at len;omega)))) := by
  let chain := annotatedRun_to_chain D pre _ _ _ entries run
  have step := FIr_Chain.adjacent chain j.val (by simp only [List.length_map,FIr_EntryIndex.length run];omega)
  simp only [List.getElem_map,pairOf,challengeOf] at step
  have mapped := congrArg (algebraMap K W) step
  rw [map_add] at mapped
  rw [← polynomial run values full j.succ,← polynomial run values full j.castSucc]
  have evalZero := Polynomial.eval_map_apply (algebraMap K W) (0:K)
    (p:=polynomialOf (entries[j.val+1]'(by rw [FIr_EntryIndex.length run];omega)).coefficients)
  have evalOne := Polynomial.eval_map_apply (algebraMap K W) (1:K)
    (p:=polynomialOf (entries[j.val+1]'(by rw [FIr_EntryIndex.length run];omega)).coefficients)
  simp only [map_zero] at evalZero
  simp only [map_one] at evalOne
  rw [evalZero,evalOne,← FIr_EntryIndex.challenge run alpha same j.castSucc,Polynomial.eval_map_apply]
  exact mapped

#print axioms polynomial
#print axioms adjacent
end AspisR1.FIr_SourceChain
end
