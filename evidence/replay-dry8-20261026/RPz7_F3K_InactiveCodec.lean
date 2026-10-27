import RPz7_F3K_WideEncoding
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_InactiveCodec
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller.OriginalSerializerInstallation
open AspisV8R19.SqueezeOracleBridge
open RetainedFieldByteCodec StrictWideByteCodec WideParserArrayHalves

theorem source_roundtrip (input : Slice U8) (value : CandidateWideParserRefinement.Wide)
    (parsed : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input=ok (some value)) :
    ∃ output,sourceBytes (F3K_WideEncoding.prepFromParsed value)=ok output ∧
      MultiproofConeCanonical.bytesOf output.val=MultiproofConeCanonical.bytesOf input.val := by
  have len := (UnrolledWideParserRefinement.slice_success_canonical input value parsed).1
  let a : Array U8 32#usize := ⟨input.val,len⟩
  have asSlice : Array.to_slice a=input := by cases input;rfl
  obtain ⟨limbs,decoded,same,encoded⟩ := UnrolledWideParserRefinement.fixed_success a value
    (by rw [asSlice];exact parsed)
  refine ⟨expectedBytes (F3K_WideEncoding.prepFromParsed value),sourceBytes_total _,?_⟩
  rw [← same,F3K_WideEncoding.encoding,encoded]
  apply List.ext_getElem
  · simp only [List.length_ofFn,MultiproofConeCanonical.bytesOf,List.length_map]
    exact len.symm
  · intro i hi hj
    simp only [List.getElem_ofFn,MultiproofConeCanonical.bytesOf,List.getElem_map,arrayBytes32]
    rfl

#print axioms source_roundtrip
end AspisR1.F3K_InactiveCodec
end
