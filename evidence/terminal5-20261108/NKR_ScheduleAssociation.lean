import NKR_ScheduleRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_ScheduleAssociation
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public Openings Selectors)
/-- Native cut's post function after instantiating260 and both230oracles at
SAME actual arguments. These are concrete definitions, not an Ops parameter. -/
def reference (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors) :
 Result (Array NQ 24#usize) := do
 let (initial,absorption)←NKI_InitialAssociation.reference p o s
 let middle←pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize initial
 pool_v1.pair_forest_semantic_terminal.add_preweighted middle 16#usize absorption
/-- Direction required by(aq)(5): the instantiated native post computes the
source stream. No inverse raw-log or output equality premise is introduced. -/
theorem source (packed : Array NQ 24#usize) (p : Public) (o : Openings) (s : Selectors)
 (hp : FIw_ArrayValue.canonical packed) (hz : FIw_ArrayValue.canonical o.z)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ out, reference packed p o s=ok out ∧
 pool_v1.pair_forest_semantic_terminal.add_schedule_lanes packed p o s=ok out ∧
 FIw_ArrayValue.canonical out := by
 obtain ⟨l,absorption,calls,hc,reads,wreads,df,dr,lanes,cut,ca,cr,cs,hi,ha⟩ :=
  NKI_InitialRoot.source p o s hz hh hl
 obtain ⟨middle,cm,hm,vm⟩ := NHU_Preweighted.result packed 0#usize l.initial2 (by decide) (by decide) hp hi
 obtain ⟨out,co,ho,vo⟩ := NHU_Preweighted.result middle 16#usize absorption (by decide) (by decide) hm ha
 refine ⟨out,?_,?_,ho⟩
 · simp only [reference,cr,bind_tc_ok]
   change (do let next←pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize l.initial2
              pool_v1.pair_forest_semantic_terminal.add_preweighted next 16#usize absorption)=ok out
   rw [cm,bind_tc_ok,co]
 · unfold pool_v1.pair_forest_semantic_terminal.add_schedule_lanes
   rw [cs,bind_tc_ok]
   change (do let next←pool_v1.pair_forest_semantic_terminal.add_preweighted packed 0#usize l.initial2
              pool_v1.pair_forest_semantic_terminal.add_preweighted next 16#usize absorption)=ok out
   rw [cm,bind_tc_ok,co]
#print source
#print axioms source
end AspisR1.NKR_ScheduleAssociation
end
