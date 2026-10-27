import JGo_TX2_Cell0_0
import JGo_TX2_Horner0_0
import JGo_TX2_Cell0_1
import JGo_TX2_Horner0_1
import JGo_TX2_Cell0_2
import JGo_TX2_Horner0_2
import JGo_TX2_Cell0_3
import JGo_TX2_Horner0_3
import JGo_TX2_Cell0_4
import JGo_TX2_Horner0_4
import JGo_TX2_Cell0_5
import JGo_TX2_Horner0_5
import JGo_TX2_Cell0_6
import JGo_TX2_Horner0_6
import FIo_Install
import RowFinish_Control
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_Round0
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
attribute [local irreducible] FIn_Polynomial.mul FIn_Primitives.add FIn_Primitives.field
  JFw_Frames.window JFx_NativeBytes.proof

def boundary : E := ⟨⟨⟨413408048#u32,1353552242#u32⟩,⟨1986715536#u32,304210493#u32⟩⟩,⟨⟨1573926966#u32,944937112#u32⟩,⟨926452302#u32,1394550192#u32⟩⟩⟩
theorem boundary_add : FIn_Primitives.add JGo_TX2_Cell0_0.value JGo_TX2_Cell0_4.value=ok boundary := by
  with_unfolding_all rfl
#print axioms boundary_add

theorem quarter_mul : SAG_StageScale.mulM JFq_Claim.scalar 536870912#u32=ok boundary := by
  with_unfolding_all rfl
#print axioms quarter_mul

theorem polynomial : FIn_ExtractInstall.polynomial (JFw_Frames.window 7527 224) JFq_Alpha0.scalar=
    ok JGo_TX2_Horner0_6.after := by
  rw [FIn_ExtractInstall.same]
  unfold FIn_Polynomial.polynomial
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_0.multiply,bind_tc_ok,JGo_TX2_Cell0_6.source,bind_tc_ok,JGo_TX2_Horner0_0.addition,bind_tc_ok]
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_1.multiply,bind_tc_ok,JGo_TX2_Cell0_5.source,bind_tc_ok,JGo_TX2_Horner0_1.addition,bind_tc_ok]
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_2.multiply,bind_tc_ok,JGo_TX2_Cell0_4.source,bind_tc_ok,JGo_TX2_Horner0_2.addition,bind_tc_ok]
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_3.multiply,bind_tc_ok,JGo_TX2_Cell0_3.source,bind_tc_ok,JGo_TX2_Horner0_3.addition,bind_tc_ok]
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_4.multiply,bind_tc_ok,JGo_TX2_Cell0_2.source,bind_tc_ok,JGo_TX2_Horner0_4.addition,bind_tc_ok]
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_5.multiply,bind_tc_ok,JGo_TX2_Cell0_1.source,bind_tc_ok,JGo_TX2_Horner0_5.addition,bind_tc_ok]
  rw [FIn_Polynomial.go,JGo_TX2_Horner0_6.multiply,bind_tc_ok,JGo_TX2_Cell0_0.source,bind_tc_ok,JGo_TX2_Horner0_6.addition,bind_tc_ok]
  rfl
#print axioms polynomial

def values (seed : FinishOps FIo_Install.W) : RowFinish_Control.RoundValues
    (FIo_Install.finishOps (.Ok ()) seed) (JFw_Frames.window 7527 224) JFq_Alpha0.scalar JFq_Claim.scalar where
  c0 := JGo_TX2_Cell0_0.value
  c4 := JGo_TX2_Cell0_4.value
  lhs := boundary
  quarter := 536870912#u32
  rhs := boundary
  value := JGo_TX2_Horner0_6.after
  field0 := JGo_TX2_Cell0_0.source
  field4 := JGo_TX2_Cell0_4.source
  add := boundary_add
  quarter_run := rfl
  multiply := quarter_mul
  evaluate := polynomial
#print axioms values
end AspisR1.JGo_TX2_Round0
end
