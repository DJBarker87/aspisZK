import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_state_before_z0
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_mark4 {H W : Type} (c : Calls) (s : Parent H W) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (val3 : K29) (r4 : core.result.Result r1_wire.ValidatedRecord r1_wire.Error) :
    erase (NNG_TreeSuffixes.f_mark4 c s alpha transcript1 val1 val3 r4) = NNG_SourceSuffixes.f_mark4 c s alpha transcript1 val1 val3 r4 := by
  simp only [NNG_TreeSuffixes.f_mark4, NNG_SourceSuffixes.f_mark4,
    erase_bindM, NMT_CallTree.erase_invoke, erase_liftM, NNG_TraceAlgebra.erase_lift,
    erase_pureM, erase_control, erase_if, erase_a3, erase_r11, erase_r10, erase_circleGuard, erase_b1, erase_mark5, erase_r9, erase_r8, erase_r7, erase_r6, erase_state_before_z0] <;> rfl
#print axioms erase_mark4
end AspisR1.NNG_TreeErasure
