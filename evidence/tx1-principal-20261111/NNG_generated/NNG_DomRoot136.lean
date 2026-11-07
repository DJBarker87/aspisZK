import NNG_CheckedCalls136
import NNG_AllPlain136
import NNG_TreeSuffixes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_DomRoot136
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree
open NNG_TraceAll136 NNG_TypedDomains136 NNG_AllPlain136

theorem root {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript Unit)
    (r11 : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) :
    All Checked (NNG_TreeSuffixes.f_a3 c s alpha claims extra state z0 before t3 z1 r11) := by
  unfold NNG_TreeSuffixes.f_a3
  apply plain Checked
  intro a
  exact done Checked _
#print axioms root

theorem copy {W : Type} (c : Calls) (s : Parent Unit W) (alpha : Alpha) (claims : Claims) (extra before : K29)
    (state : Array U8 32#usize) (z0 z1 : aspis_core.circle.SecureCirclePoint) (t3 : r1_wire.SemanticTranscript Unit)
    (bytes : Slice U8) :
    All Checked (NNG_TreeSuffixes.f_r11 c s alpha claims extra state z0 before t3 z1 bytes) := by
  unfold NNG_TreeSuffixes.f_r11
  apply plain Checked
  intro reply
  exact root c s alpha claims extra before state z0 z1 t3 reply
#print axioms copy
end AspisR1.NNG_DomRoot136
