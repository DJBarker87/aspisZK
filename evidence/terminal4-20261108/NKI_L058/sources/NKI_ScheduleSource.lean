import NKI_InitialRoot
import NHU_Preweighted
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ScheduleSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (decode)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings Selectors)
/-- Complete232 SOURCE association:260 and both230calls at starts0/16,
complete24cell result and frames. Native caller cut remains separate. -/
theorem source (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors)
 (hp : canonical packed) (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 ∃ (l : NKI_InitialInvocation.Locals) (absorption : Array NQ 16#usize) (middle out : Array NQ 24#usize),
 NKI_InitialInvocation.Clauses p o s l ∧
 NKI_InitialCuts.Cut p o s l absorption (NKI_InitialCuts.observations p o s l absorption) ![12,2,12,9,16,4,1] ∧
 pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption p o s=ok (l.initial2,absorption) ∧
 pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize l.initial2=ok middle ∧
 pool_v1.pair_forest_semantic_terminal.add_preweighted middle 16#usize absorption=ok out ∧
 pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed p o s=ok out ∧ canonical out ∧
 ∀ j,decoded out j=decoded packed j+FIx_SelectedMeaning.contribution (decoded l.initial2) 0 j.val+FIx_SelectedMeaning.contribution (decoded absorption) 16 j.val := by
 obtain ⟨l,absorption,calls,hc,reads,wreads,df,dr,lanes,cut,ca,cr,cs,hi,ha⟩ := NKI_InitialRoot.source p o s hz hh hl
 obtain ⟨middle,cm,hm,vm⟩ := NHU_Preweighted.result packed 0#usize l.initial2 (by decide) (by decide) hp hi
 obtain ⟨out,co,ho,vo⟩ := NHU_Preweighted.result middle 16#usize absorption (by decide) (by decide) hm ha
 refine ⟨l,absorption,middle,out,calls,cut,cs,cm,co,?_,ho,?_⟩
 · simp only [pool_v1.pair_forest_semantic_terminal.add_schedule_lanes,cs,cm,co,bind_tc_ok]
 · intro j
   rw [vo,vm]
   rfl
#print source
#print axioms source
end AspisR1.NKI_ScheduleSource
end
