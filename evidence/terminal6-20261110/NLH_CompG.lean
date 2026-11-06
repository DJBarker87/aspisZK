import NKI_InitialPrefix
import NLH_CompositionState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompG
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open NKI_InitialPrefix (Public)
theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (st : State) (hc : canonical claims) :
 ∃ g,step pub claims point lambda chi theta .g st=ok (.Ok {st with g := g}) ∧ Canon g ∧
 pool_v1.pair_forest_semantic_terminal.selected_claim claims 0#usize 27#usize=ok g := by
 obtain ⟨g,call,canon⟩ := JFy_SelectedRead.source claims hc 0#usize 27#usize (by decide) (by decide)
 exact ⟨g,by simp only [step,NKR_TermHorner.column,call,bind_tc_ok],canon,call⟩
#print axioms source
end AspisR1.NLH_CompG
end
