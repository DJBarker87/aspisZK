import Hiq_RuntimeHistory
import Hist_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RuntimeNonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry Hiq_RuntimeAction Hist_Nonvacuity

def actions : List Action := [.foreign (key 1#u8) 1 changed,.rollback]

theorem run_eval (ops : AdapterRw.Ops) :
    Hiq_RuntimeHistory.run ops (key 0#u8) original actions =
      (put original 1 changed,[.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val),.rollback]) := by
  have owner : (original 1).owner = key 1#u8 := by simp only [original,show (1:Nat) ≠ 0 by decide,if_false]
  have step : Hiq_RuntimeAction.apply ops (key 0#u8) original (.foreign (key 1#u8) 1 changed) =
      (put original 1 changed,.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val)) := by
    simp only [Hiq_RuntimeAction.apply,if_pos (And.intro different owner)]
  simp only [actions,Hiq_RuntimeHistory.run,step,Hiq_RuntimeAction.apply]

theorem nonempty (ops : AdapterRw.Ops) (law : ops.op36 = Hist_Authority.keyEq) :
    (Hiq_RuntimeHistory.run ops (key 0#u8) original actions).2 ≠ [] ∧
      (Hiq_RuntimeHistory.run ops (key 0#u8) original actions).1 0 = original 0 ∧
      Trace ops (key 0#u8) original
        (Hiq_RuntimeHistory.run ops (key 0#u8) original actions).2
        (Hiq_RuntimeHistory.run ops (key 0#u8) original actions).1 := by
  refine ⟨?_,?_,Hiq_RuntimeHistory.classified ops law _ _ _⟩
  · rw [run_eval]
    exact List.cons_ne_nil _ _
  · exact (Hiq_RuntimeHistory.protection ops law _ _ _ 0 (by simp [original]) initialized).2

#print axioms run_eval
#print axioms nonempty
end AspisR1.Hiq_RuntimeNonvacuity
end
