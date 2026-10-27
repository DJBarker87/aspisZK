import F3P_StrictLowParser
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_LowDecodeInjective

theorem encoding (x : SemanticCoefficientCodec.LowWide) :
    SemanticCoefficientCodec.encodeLow x=
      (SemanticCoefficientCodec.encodeLow x).take 16++List.replicate 16 0 := by
  let xs := RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x.val.re
  have numeric : WideExactLimbCodec.pairExactEquiv (xs,PAln_LowRead.zeroLimbs)=x.val := by
    apply QuadraticAlgebra.ext
    · exact Equiv.apply_symm_apply _ _
    · exact PAln_LowRead.exact_zero.trans x.property.symm
  have encoded : SemanticCoefficientCodec.encodeLow x=
      List.ofFn (RetainedFieldByteCodec.encodeQM31LE xs)++List.replicate 16 0 := by
    change FoldedLeafCodec.encodeWide x.val=_
    rw [← numeric,PAln_LowRead.encode_pair]
  rw [encoded]
  simp only [List.take_append,List.length_ofFn,Nat.sub_self,List.take_zero,List.append_nil,List.take_ofFn]
  rfl

theorem low_bytes (a b : SemanticCoefficientCodec.LowWide)
    (same : (SemanticCoefficientCodec.encodeLow a).take 16=(SemanticCoefficientCodec.encodeLow b).take 16) :
    a=b := by
  have full : SemanticCoefficientCodec.encodeLow a=SemanticCoefficientCodec.encodeLow b := by
    rw [encoding a,encoding b,same]
  have parsed := congrArg SemanticCoefficientCodec.decodeLow full
  simpa only [SemanticCoefficientCodec.decodeLow_encode,Option.some.injEq] using parsed

#print axioms encoding
#print axioms low_bytes
end AspisR1.F3P_LowDecodeInjective
end
