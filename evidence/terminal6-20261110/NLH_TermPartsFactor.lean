import NKR_TermTail
import NKI_InitialPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_TermPartsFactor
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
/-- Unconditional complete-Result factor of263. The SAME237 source call is
inside the reference, never a successful-call or endpoint root hypothesis. -/
def reference (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (zc : Array NQ 10#usize) (mu : NQ) := do
 let child←pool_v1.pair_forest_semantic_terminal.composition_parts pub claims point lambda chi theta
 NKR_TermTail.after zc point mu child

theorem source (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
 (lambda chi theta : NQ) (zc : Array NQ 10#usize) (mu : NQ) :
 pool_v1.pair_forest_semantic_terminal.terminal_parts pub claims point lambda chi theta zc mu=
 reference pub claims point lambda chi theta zc mu := by
 unfold pool_v1.pair_forest_semantic_terminal.terminal_parts reference
 cases h : pool_v1.pair_forest_semantic_terminal.composition_parts pub claims point lambda chi theta with
 | fail e => rfl
 | div => rfl
 | ok child =>
   cases child with
   | Err e => rfl
   | Ok child =>
     rcases child with ⟨comp,c1,mask,g,h,active⟩
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,NKR_TermTail.after,NKR_TermTail.tail,NKR_TermTail.arithmetic,bind_assoc_eq]
     rfl
#print source
#print axioms source
end AspisR1.NLH_TermPartsFactor
end
