import DrvC_FirstPrepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstConstants
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers

/-- Fill the already extracted literal current-caller constants as well as
Port1 release library leaves. No protocol body is replaced by a result. -/
def configuration {F C : Type} (c : Configuration F C) : Configuration F C :=
  DrvC_Implementation.release
    {c with currentBase := AspisR1CurrentCaller.ConcreteConstants.withConstants c.currentBase}

theorem split {F C : Type} (c : Configuration F C) : (stage c).op16 = ok 10#usize := rfl

theorem folded {F C : Type} (c : Configuration F C) :
    AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT (currentInstalled (configuration c)) = ok 7751#usize := by
  change (do let i ← ok 7527#usize; i + 224#usize) = ok 7751#usize
  simp only [bind_tc_ok]
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

theorem round1 {F C : Type} (c : Configuration F C) :
    AspisR1CurrentCaller.compact.OFF_ROUND1 (currentInstalled (configuration c)) = ok 7783#usize := by
  unfold AspisR1CurrentCaller.compact.OFF_ROUND1
  rw [folded]
  simp only [bind_tc_ok]
  apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

theorem stage_folded {F C : Type} (c : Configuration F C) : (stage c).op15 = ok 7751#usize := rfl

theorem stage_round1 {F C : Type} (c : Configuration F C) : (stage c).op14 = ok 7783#usize := rfl

theorem mark {F C : Type} (c : Configuration F C) (phase : VTop_Stages.verifier.Phase) :
    (stage (DrvC_Implementation.release c)).op13 none phase = ok () := rfl

#print axioms split
#print axioms folded
#print axioms round1
#print axioms stage_folded
#print axioms stage_round1
#print axioms mark
end AspisR1.DrvC_FirstConstants
end
