import NDO_JFw_TX2_Dot0
import NDO_JFw_TX2_Dot1
import NDO_JFw_TX2_Dot2
import NDO_JFw_TX2_Dot3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Dots0
open Aeneas Aeneas.Std Result
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize
  [JFw_TX2_Dot0.value,JFw_TX2_Dot1.value,JFw_TX2_Dot2.value,JFw_TX2_Dot3.value]
def value := FIp_DotsAdapter.fromArray native

theorem source : JFs_TX2_Dots.value 0=value := by
  apply JFw_TX2_DotsExplicit.chosen
  rw [JFs_TX2_FourHead.source]
  simp only [JFs_TX2_FourHead.slots,JFw_TX2_Dot0.source,JFw_TX2_Dot1.source,
    JFw_TX2_Dot2.source,JFw_TX2_Dot3.source,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JFw_TX2_Dots0
end
