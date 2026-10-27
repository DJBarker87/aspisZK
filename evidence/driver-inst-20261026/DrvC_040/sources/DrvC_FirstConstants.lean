import DrvC_FirstPrepare
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_FirstConstants
open Aeneas Aeneas.Std Result
open DrvC_Installation Tx1Q_Carriers

theorem split {F C : Type} (c : Configuration F C) : (stage c).op16 = ok 10#usize := rfl

theorem folded {F C : Type} (c : Configuration F C) :
    AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT (currentInstalled c) = ok 7751#usize := by
  unfold AspisR1CurrentCaller.compact.OFF_FOLDED_ROOT
  rfl

theorem round1 {F C : Type} (c : Configuration F C) :
    AspisR1CurrentCaller.compact.OFF_ROUND1 (currentInstalled c) = ok 7783#usize := by
  unfold AspisR1CurrentCaller.compact.OFF_ROUND1
  rw [folded]
  rfl

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
