import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_r1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_mark2 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) :
    erase (NNG_TreeSuffixes.f_mark2 c s running alpha transcript1) = NNG_SourceSuffixes.f_mark2 c s running alpha transcript1 := by
  simp only [NNG_TreeSuffixes.f_mark2, NNG_SourceSuffixes.f_mark2,
    erase_bindM, NMT_CallTree.erase_invoke, erase_liftM, NNG_TraceAlgebra.erase_lift,
    erase_pureM, erase_control, erase_if, erase_a3, erase_r11, erase_r10, erase_circleGuard, erase_b1, erase_mark5, erase_r9, erase_r8, erase_r7, erase_r6, erase_state_before_z0, erase_mark4, erase_terminalGuard, erase_b, erase_masked_terminal, erase_q3, erase_q2, erase_q1, erase_r5, erase_r4, erase_mask, erase_q, erase_a2, erase_a1, erase_a, erase_mark3, erase_r3, erase_r2, erase_r1] <;> rfl
#print axioms erase_mark2
end AspisR1.NNG_TreeErasure
