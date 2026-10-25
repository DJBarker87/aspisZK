import DrvC_PairProgram
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Bytes
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge

theorem decode_injective : Function.Injective decodeByte := by
  intro x y same
  have encoded := congrArg encodeByte same
  simpa only [word_roundtrip] using encoded

theorem list_injective (xs ys : List U8) (h : bytesOf xs = bytesOf ys) : xs = ys := by
  have restored := congrArg (List.map encodeByte) h
  simpa [bytesOf,List.map_map,Function.comp_def,word_roundtrip] using restored

theorem slice_injective (xs ys : Slice U8) (h : bytesOf xs.val = bytesOf ys.val) : xs = ys :=
  Subtype.ext (list_injective _ _ h)

theorem asSlice (s : Slice U8) : Port1_Driver.asSlice (bytesOf s.val) = some s := by
  unfold Port1_Driver.asSlice
  have size : (bytesOf s.val).length ≤ Usize.max := by simpa only [bytesOf,List.length_map] using s.property
  rw [dif_pos size]
  congr 1
  apply Subtype.ext
  change List.map (encodeByte ∘ decodeByte) s.val = s.val
  simp [Function.comp_def,word_roundtrip]

#print axioms decode_injective
#print axioms list_injective
#print axioms slice_injective
#print axioms asSlice
end AspisR1.DrvC_Bytes
end
