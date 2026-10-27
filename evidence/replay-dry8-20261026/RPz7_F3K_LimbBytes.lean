import RPz7_F3K_WordCodec
import RPz7_S1OriginalSerializerInstallationV1
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_LimbBytes
open Aeneas Aeneas.Std Result
open AspisV8R19.SqueezeOracleBridge
open RetainedFieldByteCodec

theorem source_list (w : U32) :
    AspisR1WideToBytesIndexedCandidate.limbBytes w=(core.num.U32.to_le_bytes w).val := by
  apply List.ext_getElem
  · simp only [AspisR1WideToBytesIndexedCandidate.limbBytes,List.length_cons,List.length_nil,Array.length_eq]
    rfl
  · intro i hi hj
    have hi4 : i<4 := by simpa only [AspisR1WideToBytesIndexedCandidate.limbBytes,List.length_cons,List.length_nil] using hi
    interval_cases i <;> simp only [AspisR1WideToBytesIndexedCandidate.limbBytes,core.num.U32.to_le_bytes,List.getElem_cons_zero,List.getElem_cons_succ,List.getElem_map]

theorem decoded_list (w : U32) :
    (AspisR1WideToBytesIndexedCandidate.limbBytes w).map decodeByte=
      List.ofFn (encodeWordLE ⟨w.val,w.bv.isLt⟩) := by
  rw [source_list,← F3K_WordCodec.encoding]
  apply List.ext_getElem
  · simp only [List.length_map,Array.length_eq,List.length_ofFn]
    rfl
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_ofFn,F3K_WordCodec.bytes4]

theorem canonical_limb (x : M31Value) :
    (AspisR1WideToBytesIndexedCandidate.limbBytes (M31ParserRefinement.valueToU32 x)).map decodeByte=
      List.ofFn (encodeM31LE x) := by
  rw [decoded_list]
  rfl

#print axioms source_list
#print axioms decoded_list
#print axioms canonical_limb
end AspisR1.F3K_LimbBytes
end
