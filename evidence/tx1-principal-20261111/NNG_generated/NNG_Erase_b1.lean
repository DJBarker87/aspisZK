import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_circleGuard
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_b1 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (val1 : Claims) (val3 : K29) (state_before_z0 : Array U8 32#usize) (val4 : aspis_core.circle.SecureCirclePoint) (val5 : K29) (transcript3 : r1_wire.SemanticTranscript H) (val6 : aspis_core.circle.SecureCirclePoint) :
    erase (NNG_TreeSuffixes.f_b1 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6) = NNG_SourceSuffixes.f_b1 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 := by
  simp only [NNG_TreeSuffixes.f_b1, NNG_SourceSuffixes.f_b1,
    erase_bindM, NMT_CallTree.erase_invoke, erase_liftM, NNG_TraceAlgebra.erase_lift,
    erase_pureM, erase_control, erase_if, erase_a3, erase_r11, erase_r10, erase_circleGuard] <;> rfl
#print axioms erase_b1
end AspisR1.NNG_TreeErasure
