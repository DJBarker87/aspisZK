import S4QueryReturnedSemanticsV1
import S4LocalBatchModelTransportV1
import S4FormatPayloadAlignmentV1
import OraclePortPackedChoiceC4
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4SelectedPackedReturnV1
open AspisR1Stage2
open AspisR1S4QueryReturnedSemanticsV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1S4FullQueryValuesPrefixV1 (sourceOpening)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE)
open AspisR1S4P6PowersQueryJoinV1 (stage2ToClaim)
open AspisV8R19.DuplexFrames
open OraclePortSelectedDraft (index)
open OraclePortPackedChoiceC4 (payload packed_agrees)
open OraclePortStoredDecisionDraftC4 (packed)

private theorem index_success_bound {A : Type} {n : Usize}
    (xs : Array A n) (i : Usize) (x : A)
    (h : Array.index_usize xs i = .ok x) : i.val < n.val := by
  have hlen : i.val < xs.val.length := by
    by_contra hnot
    have hnone : xs[i]? = none := List.getElem?_eq_none (Nat.not_lt.mp hnot)
    unfold Array.index_usize at h
    rw [hnone] at h
    cases h
  simpa [xs.property] using hlen

abbrev SelectedPackedReturnEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (gamma : ClaimE)
    (parsed : OraclePortCompactDraft.Parsed) (queries : Fin 22 → Fin 262144) : Prop :=
    ∃ (pos : Fin 22) (sourceIndex : U32) (sourceLeaf : Usize)
      (physical : Slice U8)
      (values : Array aspis_core.field.wide_exact.WideExact 4#usize),
      pos.val = a.next.val ∧
      Array.index_usize p.queries a.next = .ok sourceIndex ∧
      lift (UScalar.cast .Usize sourceIndex) = .ok sourceLeaf ∧
      sourceOpening proof a.next = .ok physical ∧
      (concreteCandidateQueryOps rest).dots physical g = .ok values ∧
      values.val.map (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (stage2ToClaim x)) =
      List.ofFn (fun slot : Fin 4 => FirstFold.fibre
        (TwoFoldExtraction.batchedWord
          (TypedRecoveredWords.word ExactBaseProjection.embed
            (algebraMap ExactLeafFieldCodec.QM31Exact
              AspisR1FastDotsTailFieldProductRootV1.TowerWide)
            (fun leaf => packed parsed queries 0 leaf.val)
            (fun leaf => packed parsed queries 1 leaf.val))
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) (queries pos) slot)

/-- Same physical callback values interpreted in the global first-occurrence
packed word. Authentication is the existing per-position recovery predicate;
no uniqueness of queried indices is assumed. Source/model query-sampler
correspondence is a separate upstream obligation. -/
theorem returned_values_match_selected_packed_word
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array ClaimE 29#usize) (gamma : ClaimE)
    (hret : CandidateQueryReturnedLocalBatchEvidence rest proof p a g powers gamma)
    (parsed : OraclePortCompactDraft.Parsed)
    (hlen : proof.val.length = 57607)
    (hwire : parsed.wire = MultiproofConeCanonical.bytesOf proof.val)
    (queries : Fin 22 → Fin 262144)
    (recovered0 recovered1 : Nat → Option Bytes)
    (hauth0 : ∀ pos, pos < 22 →
      recovered0 (index queries 0 pos) = some (payload parsed 0 pos))
    (hauth1 : ∀ pos, pos < 22 →
      recovered1 (index queries 1 pos) = some (payload parsed 1 pos)) :
    SelectedPackedReturnEvidence rest proof p a g gamma parsed queries := by
  obtain ⟨i,u,q,values,currentValues,arrayQ,v0,v1,v2,v3,c1,c2,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3,
    hc1,hc2,hbytes,hlocal⟩ := hret
  have hbound : a.next.val < 22 := index_success_bound p.queries a.next i hi
  let pos : Fin 22 := ⟨a.next.val,hbound⟩
  have hpayload := AspisR1S4FormatPayloadAlignmentV1.payload_partitions
    proof hlen parsed hwire a.next.val hbound q arrayQ hread ha
  have hindex0 : index queries 0 a.next.val = (queries pos).val := by
    simp only [index, Nat.mod_eq_of_lt hbound, ↓reduceIte]

  have hindex1 : index queries 1 a.next.val = (queries pos).val := by
    simp only [index, Nat.mod_eq_of_lt hbound, ↓reduceIte]

  have hpk0 := packed_agrees parsed queries 0 recovered0 hauth0 a.next.val hbound
  have hpk1 := packed_agrees parsed queries 1 recovered1 hauth1 a.next.val hbound
  have hm0 : packed parsed queries 0 (queries pos).val =
      some ((arrayQ.val.map ExtractedRecordByteValue.rawByte).take 480) := by
    calc
      packed parsed queries 0 (queries pos).val = recovered0 (queries pos).val := by
        simpa only [hindex0] using hpk0
      _ = some (payload parsed 0 a.next.val) := by
        simpa only [hindex0] using hauth0 a.next.val hbound
      _ = _ := congrArg some hpayload.1
  have hm1 : packed parsed queries 1 (queries pos).val =
      some ((arrayQ.val.map ExtractedRecordByteValue.rawByte).drop 480) := by
    calc
      packed parsed queries 1 (queries pos).val = recovered1 (queries pos).val := by
        simpa only [hindex1] using hpk1
      _ = some (payload parsed 1 a.next.val) := by
        simpa only [hindex1] using hauth1 a.next.val hbound
      _ = _ := congrArg some hpayload.2
  have hmodel := S4LocalBatchModelTransportV1.four_slot_local_batches_are_model_inputs
    ExactBaseProjection.embed
    (algebraMap ExactLeafFieldCodec.QM31Exact AspisR1FastDotsTailFieldProductRootV1.TowerWide)
    (fun leaf => packed parsed queries 0 leaf.val)
    (fun leaf => packed parsed queries 1 leaf.val) (queries pos)
    (arrayQ.val.map ExtractedRecordByteValue.rawByte) c1 c2
    (AspisR1CurrentPreparedClaim.Concrete.decode gamma) hm0 hm1 hc1 hc2
  exact ⟨pos,i,u,q,values,rfl,hi,hu,hopening,hdots,hlocal.trans hmodel⟩
#print axioms returned_values_match_selected_packed_word
end AspisR1.S4SelectedPackedReturnV1
