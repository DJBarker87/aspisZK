import NMT_345Encoder
set_option autoImplicit false
noncomputable section
namespace NMT_R2_EncoderTotal
open Aeneas Aeneas.Std NMT_345

def value (a : Afterstate) : core.result.Result (Array U8 688#usize) EncodeError :=
 mapCore id NMT_345Dec.fromT11
  (match NFY_NBH_Validators.afterResult (NMT_345Dec.toT5 a) with
   | .Ok _ => .Ok (AspisR1.S2K.AfterstateEncoding.bytes (NMT_345Dec.toT5 a))
   | .Err e => .Err e)

/-- Full CLOSED278 source law, all afterstates and BOTH Result arms. The
existing symbolic encoder theorem is reused without reducing its688 bytes. -/
theorem source (a : Afterstate) : encodeCall a = .ok (value a) := by
 unfold encodeCall
 rw [NFY_NBK_AfterstateResult.source]
 rfl

theorem total (a : Afterstate) : ∃ r, encodeCall a = .ok r := ⟨value a,source a⟩
#print axioms source
#print axioms total
end NMT_R2_EncoderTotal
end
