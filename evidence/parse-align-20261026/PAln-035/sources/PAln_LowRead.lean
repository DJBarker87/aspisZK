import PAln_FieldRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_LowRead
open AspisV8R19.DuplexFrames OraclePortCompactDraft
open RetainedFieldByteCodec StrictWideByteCodec WideExactLimbCodec

def zeroLimbs : QM31Limbs := fun _ => 0

theorem exact_zero : RetainedExactLimbCodec.qm31ExactLimbEquiv zeroLimbs=0 := by
  simp only [RetainedExactLimbCodec.qm31ExactLimbEquiv_apply,
    RetainedExactLimbCodec.limbsToQM31Exact,zeroLimbs,map_zero]
  rfl

theorem encoded_zero : List.ofFn (encodeQM31LE zeroLimbs)=List.replicate 16 0 := by
  have same : encodeQM31LE zeroLimbs=(fun _ => 0) := by
    funext i
    unfold encodeQM31LE zeroLimbs encodeM31LE m31AsRawWord encodeWordLE
    simp
  rw [same]
  simp

theorem encode_pair (lo : QM31Limbs) :
    FoldedLeafCodec.encodeWide (pairExactEquiv (lo,zeroLimbs))=
      List.ofFn (encodeQM31LE lo)++List.replicate 16 0 := by
  simp only [FoldedLeafCodec.encodeWide,Equiv.symm_apply_apply,encodeWideLE,
    List.ofFn_fin_append,encoded_zero]

theorem low_exists (b : Bytes) (length : b.length=16) (checked : canonical b) :
    ∃ value : SemanticCoefficientCodec.LowWide,
      SemanticCoefficientCodec.decodeLow (b++List.replicate 16 0)=some value := by
  let f : Fin 16 → Fin 256 := fun i => b[i.val]'(by omega)
  have same : List.ofFn f=b := by
    apply List.ext_getElem
    · simp [length]
    · intro i hi hj
      simp only [List.getElem_ofFn,f]
  obtain ⟨lo,decoded⟩ := PAln_FieldRead.qm31_exists f (same.symm ▸ checked)
  let value := pairExactEquiv (lo,zeroLimbs)
  have upper : value.im=0 := by
    change (RetainedExactLimbCodec.qm31ExactLimbEquiv zeroLimbs)=0
    exact exact_zero
  let low : SemanticCoefficientCodec.LowWide := ⟨value,upper⟩
  have encoded : SemanticCoefficientCodec.encodeLow low=b++List.replicate 16 0 := by
    change FoldedLeafCodec.encodeWide (pairExactEquiv (lo,zeroLimbs))=_
    rw [encode_pair,encodeQM31LE_of_decodeQM31LE f lo decoded,same]
  refine ⟨low,?_⟩
  rw [← encoded]
  exact SemanticCoefficientCodec.decodeLow_encode low

#print axioms exact_zero
#print axioms encoded_zero
#print axioms encode_pair
#print axioms low_exists
end AspisR1.PAln_LowRead
end
