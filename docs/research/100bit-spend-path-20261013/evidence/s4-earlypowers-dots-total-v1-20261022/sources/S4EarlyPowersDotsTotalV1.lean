import S4QueryOpsTotalLocalValuesV1
import S4EarlyPowersSourceBindingV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4EarlyPowersDotsTotalV1
open AspisR1Stage2
open AspisR1S4P6PowersQueryJoinV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4EarlyPowersSourceBindingV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

/-- The generated candidate powers body followed by the installed dots slot
is total and exact on a canonical gamma and a strictly scanned opening. All
powers-success, coefficient-array and dots-success witnesses are derived. -/
theorem earlypowers_then_dots_total_exact_batches
    (rest : QueryOps) (proof : Slice U8) (j : Nat) (q : Slice U8)
    (gamma : Stage2Wide) (hgamma : ClaimCanonical (stage2ToClaim gamma))
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (g : Stage2Array), ∃ values, ∃ (a : Array U8 608#usize) (c1 : C1) (c2 : C2),
      extractedEarlyWeightsPowers 29#usize gamma = .ok g ∧
      (concreteCandidateQueryOps rest).dots q g = .ok values ∧
      (do let coefficients ← extractedEarlyWeightsPowers 29#usize gamma
          (concreteCandidateQueryOps rest).dots q coefficients) = .ok values ∧
      a.val = q.val.slice 0 (608#usize) ∧
      decodeC1 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      values.val.map (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (stage2ToClaim x)) =
        List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode (stage2ToClaim gamma))) := by
  obtain ⟨powers,hpowers,hmeaning⟩ :=
    AspisR1CurrentPreparedClaim.ClaimPowers.powers_total_exact
      29#usize (stage2ToClaim gamma) hgamma
  let g := claimArrayToStage2 powers
  have hg : extractedEarlyWeightsPowers 29#usize gamma = .ok g := by
    rw [extractedEarlyWeightsPowers_eq_claimPowers, hpowers]
    rfl
  have hcaller : fullArrayToCurrent g = claimArrayToFast powers := by
    apply Subtype.ext
    change (powers.val.map claimToStage2).map fullWideToCurrent =
      powers.val.map claimToFast
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    cases x <;> rfl
  obtain ⟨values,a,c1,c2,hdots,ha,hd1,hd2,hvalues⟩ :=
    AspisR1.S4QueryOpsTotalLocalValuesV1.candidate_queryops_dots_total_exact_batches
      rest proof j q g (stage2ToClaim gamma) powers hgamma hpowers hcaller hlen hj hread hscan
  refine ⟨g,values,a,c1,c2,hg,hdots,?_,ha,hd1,hd2,hvalues⟩
  rw [hg, bind_tc_ok]
  exact hdots

#print axioms earlypowers_then_dots_total_exact_batches
end AspisR1.S4EarlyPowersDotsTotalV1
