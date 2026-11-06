import NKI_InitialPrefix
import NLH_CompositionState
import NJB_PreparedLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompPrepared
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKI_InitialPrefix (Public)
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) (ht : Canon theta) :
 ∃ p,step pub claims point lambda chi theta .prepare st=
  ok (.Ok {st with prepared := p,composition := st.copy.residual, remaining := st.semantic.val.reverse ++ st.poseidon.val.reverse}) ∧
 NJB_PreparedLaws.Domain p theta ∧ field.PreparedQm31Multiplier.new theta=ok p := by
 obtain ⟨p,call,domain⟩ := NJB_PreparedLaws.new_result theta ht
 exact ⟨p,by simp only [step,call,bind_tc_ok],domain,call⟩
#print axioms source
end AspisR1.NLH_CompPrepared
end
