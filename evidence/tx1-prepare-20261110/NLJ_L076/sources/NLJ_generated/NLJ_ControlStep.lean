import NLJ_ControlParse
import NLJ_ControlPublic
import NLJ_ControlBegin
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (run)
/-- Complete per-occurrence substitution table. Every CLOSED result clause is
DISCHARGED here; no free closed-child Result/success/endpoint is a premise.
Only the exact OPEN136 packet survives, under (bd). Physical cut admission is
still separate and is not asserted by this source/control model equation. -/
theorem source_step
 (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit)
 (child136 : NLI_Interface.RowSpec_136 native136) (s : NLJ_Observed.State Unit) :
 step native136 s = run (NLJ_Observed.step s) := by
 cases s with
 | mk i locals =>
   cases locals with
   | parse =>
     unfold step
     rw [parser]
     rfl
   | mark0 p => rfl
   | publicTranscript p => exact public_step native136 i p
   | begin p t => exact begin_step native136 i p t
   | mark1 p t c => rfl
   | finish p t c => exact (NLJ_Observed.finish_packet native136 child136 i p t c).2.symm
#print axioms source_step
#print source_step
end AspisR1.NLJ_Control137
end
