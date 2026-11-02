import NEO_WideReference
set_option autoImplicit false
namespace NEO_WideTotal
open Aeneas Aeneas.Std Result AspisR1
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

def cohort (bytes : Slice U8) : Result (Option (Array U32 8#usize)) := do
 let o ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
 match o with
 | none => ok none
 | some x => do let w ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x; ok (some w)

theorem wrong_length (bytes : Slice U8) (wrong : bytes.val.length≠32) :
 NEO_WindowV2.wide bytes=ok none := by
 have ne : Slice.len bytes != 32#usize := by
  simp only [bne_iff_ne]
  intro h
  have val := congrArg UScalar.val h
  apply wrong
  change bytes.val.length=32 at val
  exact val
 simp only [NEO_WindowV2.wide,ne,if_true]

theorem result (bytes : Slice U8) : NEO_WindowV2.wide bytes=cohort bytes := by
 by_cases len : bytes.val.length=32
 · let a : Array U8 32#usize := ⟨bytes.val,len⟩
   have same : a.to_slice=bytes := by cases bytes; rfl
   rw [←same]
   exact NEO_WideReference.result a
 · rw [wrong_length bytes len]
   unfold cohort
   rw [NBG_WideCarriers.wrong_byte_length bytes len]
   rfl

theorem option_lossless (x y : Option E)
 (same : x.map NEB_ArrayRefs.wordsE=y.map NEB_ArrayRefs.wordsE) : x=y :=
 NEO_ParserTotal.option_lossless x y same

theorem frame {S Event : Type} (state : S) (bytes : Slice U8) :
 NEB_PureFrame.run (Event:=Event) state (NEO_WindowV2.wide bytes)=
 NEB_PureFrame.run state (cohort bytes) := NEB_PureFrame.equality state _ _ (result bytes)

#print axioms wrong_length
#print axioms result
#print axioms option_lossless
#print axioms frame
end NEO_WideTotal
