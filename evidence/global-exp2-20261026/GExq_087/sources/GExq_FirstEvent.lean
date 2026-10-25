import GExq_RecordTrace
set_option autoImplicit false
namespace AspisR1.GExq_FirstEvent
open Aeneas Aeneas.Std Result

theorem occurrence (log : S2W_Trace.Log)
    (semantic : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (member : GExq_OuterRecord.Event.first semantic pub proof split (.Ok saved) ∈ GExq_RecordTrace.projectLog log) :
    ∃ (Hash : Type) (D : AdapterRw.aspis_core.digest.Digest32 Hash) (hash : Hash)
      (obs : Option (AdapterRw.aspis_r1_cost_probe.verifier.Phase → Result Unit)),
      S2W_Trace.Event.returned (.op10 D semantic pub proof split hash obs) (.Ok saved) ∈ log := by
  obtain ⟨event,belongs,projected⟩ := List.mem_flatMap.mp member
  cases event with
  | returned call value =>
    cases call <;> simp only [GExq_OuterRecord.project,List.not_mem_nil,List.mem_singleton] at projected
    all_goals try contradiction
    all_goals cases projected
    all_goals exact ⟨_,_,_,_,belongs⟩

#print axioms occurrence
end AspisR1.GExq_FirstEvent
