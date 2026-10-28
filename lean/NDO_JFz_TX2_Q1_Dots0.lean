import NDO_JFz_TX2_Q1_Dot0
import NDO_JFz_TX2_Q1_Dot1
import NDO_JFz_TX2_Q1_Dot2
import NDO_JFz_TX2_Q1_Dot3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFz_TX2_Q1_Dot0.value,JFz_TX2_Q1_Dot1.value,JFz_TX2_Q1_Dot2.value,JFz_TX2_Q1_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 1=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFz_TX2_Q1_Dot0.source,JFz_TX2_Q1_Dot1.source,
    JFz_TX2_Q1_Dot2.source,JFz_TX2_Q1_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFz_TX2_Q1_Dots0
end
