import F3S_RoundValues
set_option autoImplicit false
namespace AspisR1.F3S_RoundUnique
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
 theorem values {W : Type} (ops : FinishOps W) (bytes : Slice U8) (alpha claim : E)
    (r s : RowFinish_Control.RoundValues ops bytes alpha claim) :
    r.lhs=s.lhs ∧ r.rhs=s.rhs ∧ r.value=s.value := by
  have c0 : r.c0=s.c0 := Result.ok.inj (r.field0.symm.trans s.field0)
  have c4 : r.c4=s.c4 := Result.ok.inj (r.field4.symm.trans s.field4)
  have quarter : r.quarter=s.quarter := Result.ok.inj (r.quarter_run.symm.trans s.quarter_run)
  refine ⟨?_,?_,Result.ok.inj (r.evaluate.symm.trans s.evaluate)⟩
  · have left := r.add
    rw [c0,c4] at left
    exact Result.ok.inj (left.symm.trans s.add)
  · have right := r.multiply
    rw [quarter] at right
    exact Result.ok.inj (right.symm.trans s.multiply)
#print axioms values
end AspisR1.F3S_RoundUnique
