import NMX_ScalarCarrier
set_option autoImplicit false
namespace NMX_KeyCarrier
open Aeneas Aeneas.Std NMX_Carrier NMX_ScalarCarrier
attribute [local instance] Classical.propDecidable

theorem key_injective : Function.Injective key := by
 intro a b same
 apply Subtype.ext
 exact (List.map_inj_right (fun x y h => byte_injective h)).mp
  (congrArg RSL.B32.bytes same)

theorem key_equal (a b : Array U8 32#usize) : key a = key b ↔ a = b :=
 ⟨fun same => key_injective same,fun same => congrArg key same⟩

theorem key_length (a : Array U8 32#usize) : (key a).bytes.length = 32 := (key a).len

theorem slice_length (a : Slice U8) : (bytes a).length = a.val.length := by simp only [bytes,List.length_map]

/-- Native/model comparison consumes the entire key, without a byte-window
or canonical-field hypothesis. -/
theorem decide_equal (a b : Array U8 32#usize) :
 decide (key a = key b) = decide (a = b) := by
 classical
 simp only [key_equal]
#print axioms key_injective
#print axioms key_equal
#print axioms key_length
#print axioms slice_length
#print axioms decide_equal
end NMX_KeyCarrier
