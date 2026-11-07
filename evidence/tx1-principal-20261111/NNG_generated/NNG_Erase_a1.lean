import NNG_TreeSuffixes
import NNG_SourceSuffixes
import NNG_TraceCongruence
import NNG_Erase_a2
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
theorem erase_a1 {H W : Type} (c : Calls) (s : Parent H W) (running : Q) (val2 : Q) (alpha : Alpha) (transcript1 : r1_wire.SemanticTranscript H) (val1 : Claims) (a : Array Q 16#usize) :
    erase (NNG_TreeSuffixes.f_a1 c s running val2 alpha transcript1 val1 a) = NNG_SourceSuffixes.f_a1 c s running val2 alpha transcript1 val1 a := by
  simp only [NNG_TreeSuffixes.f_a1, NNG_SourceSuffixes.f_a1,
    erase_bindM, NMT_CallTree.erase_invoke, erase_liftM, NNG_TraceAlgebra.erase_lift,
    erase_pureM, erase_control, erase_if, erase_a3, erase_r11, erase_r10, erase_circleGuard, erase_b1, erase_mark5, erase_r9, erase_r8, erase_r7, erase_r6, erase_state_before_z0, erase_mark4, erase_terminalGuard, erase_b, erase_masked_terminal, erase_q3, erase_q2, erase_q1, erase_r5, erase_r4, erase_mask, erase_q, erase_a2] <;> rfl
#print axioms erase_a1
end AspisR1.NNG_TreeErasure
