import RPz7_F3P_LowLimbMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_StrictLowParser
open Aeneas Aeneas.Std Result
open RetainedFieldByteCodec

theorem parsed (arr : Array U8 16#usize) (q : ActualDecodeKFieldParserTransport.ActualQ)
    (success : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)=ok (some q)) :
    ∃ value : SemanticCoefficientCodec.LowWide,
      SemanticCoefficientCodec.decodeLow
        (MultiproofConeCanonical.bytesOf arr.val++List.replicate 16 0)=some value ∧
      value.val=LiteralOpeningView.eK (F3L_RhoMeaning.decode (AspisS1ExtractedRoundChildren.decoderQMToMain q)) := by
  obtain ⟨limbs,decoded,same,encoded⟩ := ActualDecodeKStrictQM31Parser.success_has_strict_limbs arr q success
  subst q
  let value := WideExactLimbCodec.pairExactEquiv (limbs,PAln_LowRead.zeroLimbs)
  have upper : value.im=0 := PAln_LowRead.exact_zero
  let low : SemanticCoefficientCodec.LowWide := ⟨value,upper⟩
  have bytes : MultiproofConeCanonical.bytesOf arr.val=List.ofFn (CandidateParserByteOrder.arrayBytes16 arr) := by
    apply List.ext_getElem
    · simp only [MultiproofConeCanonical.bytesOf,List.length_map,List.length_ofFn];exact arr.property
    · intro i hi hj
      simp only [MultiproofConeCanonical.bytesOf,List.getElem_map,List.getElem_ofFn,CandidateParserByteOrder.arrayBytes16]
  have encoding : SemanticCoefficientCodec.encodeLow low=MultiproofConeCanonical.bytesOf arr.val++List.replicate 16 0 := by
    change FoldedLeafCodec.encodeWide (WideExactLimbCodec.pairExactEquiv (limbs,PAln_LowRead.zeroLimbs))=_
    rw [PAln_LowRead.encode_pair,encoded,bytes]
  refine ⟨low,?_,?_⟩
  · rw [← encoding];exact SemanticCoefficientCodec.decodeLow_encode low
  · exact (F3P_LowLimbMeaning.embed limbs).symm.trans
      (congrArg LiteralOpeningView.eK (F3P_DecodeLimbMeaning.numeric limbs)).symm

#print axioms parsed
end AspisR1.F3P_StrictLowParser
end
