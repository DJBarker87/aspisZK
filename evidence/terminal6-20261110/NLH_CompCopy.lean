import NKI_InitialPrefix
import NLH_CompositionState
import RPv_JGa_Copy
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompCopy
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
/-- SAME218 arguments and both returned channels. Native optimized-to-cohort
transport is the NKR218 candidate, conditional on the combined gate. -/
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) (hz : canonical st.openings.z) (hh1 : Canon st.h)
 (hh : canonical st.selectors.high) (hl : canonical st.selectors.low) (hlam : Canon lambda) (hchi : Canon chi) :
 ∃ copy,step pub claims point lambda chi theta .copy st=ok (.Ok {st with copy := copy}) ∧
 Canon copy.residual ∧ Canon copy.active ∧
 pool_v1.pair_forest_copy_terminal.evaluate_with_selectors st.openings.z st.h st.selectors lambda chi
   pub.transition.live_snapshot.next_pair_index st.copyVariant=ok copy := by
 obtain ⟨copy,call,cr,ca⟩ := JGa_Copy.source st.openings.z st.h st.selectors lambda chi
   pub.transition.live_snapshot.next_pair_index st.copyVariant hz hh1 hh hl hlam hchi
 exact ⟨copy,by simp only [step,call,bind_tc_ok],cr,ca,call⟩
#print axioms source
end AspisR1.NLH_CompCopy
end
