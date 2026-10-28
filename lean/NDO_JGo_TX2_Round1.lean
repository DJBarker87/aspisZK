import NDO_JGo_TX2_Cell1_0
import NDO_JGo_TX2_Horner1_0
import NDO_JGo_TX2_Cell1_1
import NDO_JGo_TX2_Horner1_1
import NDO_JGo_TX2_Cell1_2
import NDO_JGo_TX2_Horner1_2
import NDO_JGo_TX2_Cell1_3
import NDO_JGo_TX2_Horner1_3
import NDO_JGo_TX2_Cell1_4
import NDO_JGo_TX2_Horner1_4
import NDO_JGo_TX2_Cell1_5
import NDO_JGo_TX2_Horner1_5
import NDO_JGo_TX2_Cell1_6
import NDO_JGo_TX2_Horner1_6
import RPt_JFq_Claim
import RPt_JFq_Alpha0
import RPt_JFq_Alpha1
import RPz7_FIo_Install
import RowFinish_Control
import NDO_JGo_TX2_Horner0_6
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Round1
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
attribute [local irreducible] FIn_Polynomial.mul FIn_Primitives.add FIn_Primitives.field
  JFw_Frames.window JFx_NativeBytes.proof

def boundary : E := ⟨⟨⟨2130493467#u32,1566509482#u32⟩,⟨833742662#u32,1427910703#u32⟩⟩,⟨⟨1951477461#u32,1315214407#u32⟩,⟨629538960#u32,1498096122#u32⟩⟩⟩
theorem boundary_add : FIn_Primitives.add JGo_TX2_Cell1_0.value JGo_TX2_Cell1_4.value=ok boundary := by
  with_unfolding_all rfl
#print axioms boundary_add

theorem quarter_mul : SAG_StageScale.mulM JGo_TX2_Horner0_6.after 536870912#u32=ok boundary := by
  with_unfolding_all rfl
#print axioms quarter_mul

theorem polynomial : FIn_ExtractInstall.polynomial (JFw_Frames.window 7783 224) JFq_Alpha1.scalar=
    ok JGo_TX2_Horner1_6.after := by
  rw [FIn_ExtractInstall.same]
  unfold FIn_Polynomial.polynomial
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_0.alpha [6#usize,5#usize,4#usize,3#usize,2#usize,1#usize,0#usize] JGo_TX2_Horner1_0.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_0.multiply,bind_tc_ok,JGo_TX2_Cell1_6.source,bind_tc_ok,JGo_TX2_Horner1_0.addition,bind_tc_ok]
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_1.alpha [5#usize,4#usize,3#usize,2#usize,1#usize,0#usize] JGo_TX2_Horner1_1.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_1.multiply,bind_tc_ok,JGo_TX2_Cell1_5.source,bind_tc_ok,JGo_TX2_Horner1_1.addition,bind_tc_ok]
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_2.alpha [4#usize,3#usize,2#usize,1#usize,0#usize] JGo_TX2_Horner1_2.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_2.multiply,bind_tc_ok,JGo_TX2_Cell1_4.source,bind_tc_ok,JGo_TX2_Horner1_2.addition,bind_tc_ok]
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_3.alpha [3#usize,2#usize,1#usize,0#usize] JGo_TX2_Horner1_3.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_3.multiply,bind_tc_ok,JGo_TX2_Cell1_3.source,bind_tc_ok,JGo_TX2_Horner1_3.addition,bind_tc_ok]
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_4.alpha [2#usize,1#usize,0#usize] JGo_TX2_Horner1_4.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_4.multiply,bind_tc_ok,JGo_TX2_Cell1_2.source,bind_tc_ok,JGo_TX2_Horner1_4.addition,bind_tc_ok]
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_5.alpha [1#usize,0#usize] JGo_TX2_Horner1_5.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_5.multiply,bind_tc_ok,JGo_TX2_Cell1_1.source,bind_tc_ok,JGo_TX2_Horner1_5.addition,bind_tc_ok]
  change FIn_Polynomial.go (JFw_Frames.window 7783 224) JGo_TX2_Horner1_6.alpha [0#usize] JGo_TX2_Horner1_6.before=ok JGo_TX2_Horner1_6.after
  rw [FIn_Polynomial.go,JGo_TX2_Horner1_6.multiply,bind_tc_ok,JGo_TX2_Cell1_0.source,bind_tc_ok,JGo_TX2_Horner1_6.addition,bind_tc_ok]
  rfl
#print axioms polynomial

def values (seed : FinishOps FIo_Install.W) : RowFinish_Control.RoundValues
    (FIo_Install.finishOps (.Ok ()) seed) (JFw_Frames.window 7783 224) JFq_Alpha1.scalar JGo_TX2_Horner0_6.after where
  c0 := JGo_TX2_Cell1_0.value
  c4 := JGo_TX2_Cell1_4.value
  lhs := boundary
  quarter := 536870912#u32
  rhs := boundary
  value := JGo_TX2_Horner1_6.after
  field0 := JGo_TX2_Cell1_0.source
  field4 := JGo_TX2_Cell1_4.source
  add := boundary_add
  quarter_run := rfl
  multiply := quarter_mul
  evaluate := polynomial
#print axioms values
end AspisR1.JGo_TX2_Round1
end
