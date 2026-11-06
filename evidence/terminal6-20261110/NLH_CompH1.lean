import NKI_InitialPrefix
import NLH_CompositionState
import NLH_TermComposeTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompH1
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) (hc : canonical claims) :
 ∃ h,step pub claims point lambda chi theta .h st=ok (.Ok {st with h := h}) ∧ Canon h ∧
 pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize 26#usize=ok h := by
 obtain ⟨h,call,canon⟩ := JFy_SelectedRead.source claims hc 0#usize 26#usize (by decide) (by decide)
 exact ⟨h,by simp only [step,NLH_TermComposeTail.hcolumn,call,bind_tc_ok],canon,call⟩
#print axioms source
end AspisR1.NLH_CompH1
end
