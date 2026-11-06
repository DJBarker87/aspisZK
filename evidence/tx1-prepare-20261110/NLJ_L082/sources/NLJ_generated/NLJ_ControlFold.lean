import NLJ_ControlInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLJ_Control137
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open PreparedHashCode (Log)
open NLJ_Observed
/-- Conditional (bd) fold, parameterized ONLY by the exact OPEN136 packet and
the proposed own cut relation. This is NOT an admitted row root: K028/K029
leave physical Prefix/frame realization open. -/
theorem source_cuts
 (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit)
 (child136 : NLI_Interface.RowSpec_136 native136)
 {n : Nat} {s : State Unit} {out : Result (Out Unit)} {log : Log}
 {events : List Event} {last : Input Unit}
 (cuts : Invocation native136 n s out log events last) :
 NLJ_Observed.Invocation n s out log events ∧ last = s.input := by
 induction cuts with
 | returned _ head => exact ⟨.returned (by rw [←source_step native136 child136];exact head),rfl⟩
 | fail _ head => exact ⟨.fail (by rw [←source_step native136 child136];exact head),rfl⟩
 | div _ head => exact ⟨.div (by rw [←source_step native136 child136];exact head),rfl⟩
 | @next n s after out log suffix events last domain head tail ih =>
   have actual : PreparedHashCode.run (NLJ_Observed.step s) = (log,ok (.inr after)) := by
     rw [←source_step native136 child136];exact head
   have frame := NLJ_Observed.input_frame s after (congrArg Prod.snd actual)
   exact ⟨.next actual ih.1,ih.2.trans frame⟩

theorem observed_fold
 (native136 : NLC_Finish.Input Unit → NLI_Interface.Observation Unit)
 (child136 : NLI_Interface.RowSpec_136 native136)
 (i : Input Unit) (out : Result (Out Unit)) (log : Log) (events : List Event) (last : Input Unit)
 (cuts : Invocation native136 6 (initial i) out log events last) :
 PreparedHashCode.run (S1SemanticCode.verify
  (S1SemanticCode.finish NJM_RoundJoin.R (IDa_Deployed.boundaries i.reservation))
  i.digest i.publicValue i.bytes i.hash none) = (log,out) ∧ last = i := by
 obtain ⟨source,frame⟩ := source_cuts native136 child136 cuts
 exact ⟨events_from_cuts i out log events source,frame⟩
#print axioms source_cuts
#print axioms observed_fold
#print observed_fold
end AspisR1.NLJ_Control137
end
