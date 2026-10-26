import F3P_StrictLowParser
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3P_LowDecodeInjective

theorem low_bytes (a b : SemanticCoefficientCodec.LowWide)
    (same : (SemanticCoefficientCodec.encodeLow a).take 16=(SemanticCoefficientCodec.encodeLow b).take 16) :
    a=b := by
  apply Subtype.ext
  apply QuadraticAlgebra.ext
  · have lower (x : SemanticCoefficientCodec.LowWide) :
        (SemanticCoefficientCodec.encodeLow x).take 16=
          List.ofFn (RetainedFieldByteCodec.encodeQM31LE
            (RetainedExactLimbCodec.qm31ExactLimbEquiv.symm x.val.re)) := by
      unfold SemanticCoefficientCodec.encodeLow FoldedLeafCodec.encodeWide
      simp only [StrictWideByteCodec.encodeWideLE,List.ofFn_fin_append]
      simp
    rw [lower,lower] at same
    have decoded := congrArg (fun bs=>ListFieldCodec.fixedBytes? 16 bs) same
    simp only [ListFieldCodec.fixedBytes?_ofFn,Option.some.injEq] at decoded
    have back := congrArg RetainedFieldByteCodec.decodeQM31LE decoded
    simp only [RetainedFieldByteCodec.decodeQM31LE_encodeQM31LE,Option.some.injEq] at back
    exact congrArg RetainedExactLimbCodec.qm31ExactLimbEquiv back
  · exact a.property.trans b.property.symm

#print axioms low_bytes
end AspisR1.F3P_LowDecodeInjective
end
