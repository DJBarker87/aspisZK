import F3M_WideMeaning
import F3K_InactiveCodec
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_InactiveReader
open Aeneas Aeneas.Std Result
open RetainedFieldByteCodec StrictWideByteCodec WideParserArrayHalves
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem parsed (input : Slice U8) (value : CandidateWideParserRefinement.Wide)
    (parsed : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled input=ok (some value)) :
    FoldedLeafCodec.decodeWide (MultiproofConeCanonical.bytesOf input.val)=
      some (decode (toClaimE (F3K_WideEncoding.prepFromParsed value))) := by
  have len := (UnrolledWideParserRefinement.slice_success_canonical input value parsed).1
  let a : Array U8 32#usize := ⟨input.val,len⟩
  have sameSlice : Array.to_slice a=input := by cases input;rfl
  obtain ⟨limbs,decoded,same,encoded⟩ := UnrolledWideParserRefinement.fixed_success a value
    (by rw [sameSlice];exact parsed)
  rw [← same,F3M_WideMeaning.limbs]
  have physical : MultiproofConeCanonical.bytesOf input.val=List.ofFn (arrayBytes32 a) := by
    apply List.ext_getElem
    · simp only [MultiproofConeCanonical.bytesOf,List.length_map,List.length_ofFn]
      exact len
    · intro i hi hj
      simp only [MultiproofConeCanonical.bytesOf,List.getElem_map,List.getElem_ofFn,arrayBytes32]
      rfl
  rw [physical]
  simp only [FoldedLeafCodec.decodeWide,ListFieldCodec.fixedBytes?_ofFn,Option.bind_some,decoded,Option.map_some]

#print axioms parsed
end AspisR1.F3M_InactiveReader
end
