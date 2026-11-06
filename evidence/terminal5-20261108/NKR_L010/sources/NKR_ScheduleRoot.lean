import NKR_ScheduleCut
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_ScheduleRoot
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open NKI_InitialPrefix (Public Openings Selectors)
/--232 complete SAME-call source/typed-cut/root association. NKI260 is a
candidate child, conditional on next-ledger adoption. Both230calls are CLOSED.
Native cut transport is P6/D188 option-A reclassification, not discharge. -/
theorem source (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors)
 (hp : canonical packed) (hz : canonical o.z) (hh : canonical s.high) (hl : canonical s.low) :
 ∃ (l : NKI_InitialInvocation.Locals) (absorption : Array NQ 16#usize) (middle out : Array NQ 24#usize),
 NKI_InitialInvocation.Clauses p o s l ∧
 pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption p o s=ok (l.initial2,absorption) ∧
 pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize l.initial2=ok middle ∧
 pool_v1.pair_forest_semantic_terminal.add_preweighted middle 16#usize absorption=ok out ∧
 NKR_ScheduleCut.Cut packed p o s l.initial2 absorption middle out
  (NKR_ScheduleCut.observations packed p o s l.initial2 absorption middle out) ∧
 pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed p o s=ok out ∧ canonical out ∧
 ∀ j,decoded out j=decoded packed j+FIx_SelectedMeaning.contribution (decoded l.initial2) 0 j.val+FIx_SelectedMeaning.contribution (decoded absorption) 16 j.val := by
 obtain ⟨l,absorption,middle,out,calls,_,child,first,second,parent,co,value⟩ :=
  NKI_ScheduleSource.source packed p o s hp hz hh hl
 exact ⟨l,absorption,middle,out,calls,child,first,second,
  NKR_ScheduleCut.source packed p o s l.initial2 absorption middle out,parent,co,value⟩
#print source
#print axioms source
end AspisR1.NKR_ScheduleRoot
end
