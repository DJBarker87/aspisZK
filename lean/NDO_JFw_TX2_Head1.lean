import NDO_JFw_TX2_Head1Lo
import NDO_JFw_TX2_Head1Hi
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Head1
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨67618853#u32,2131009323#u32⟩,⟨1541626496#u32,237461256#u32⟩⟩,⟨⟨701575401#u32,413997160#u32⟩,⟨1284607464#u32,237657178#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 0 1 0 0 26%2147483647=67618853 := JFw_TX2_Head1Lo.lane0
theorem lane1 : JFv_TX2_InnerMeaning.sum 0 1 1 0 26%2147483647=2131009323 := JFw_TX2_Head1Lo.lane1
theorem lane2 : JFv_TX2_InnerMeaning.sum 0 1 2 0 26%2147483647=1541626496 := JFw_TX2_Head1Lo.lane2
theorem lane3 : JFv_TX2_InnerMeaning.sum 0 1 3 0 26%2147483647=237461256 := JFw_TX2_Head1Lo.lane3
theorem lane4 : JFv_TX2_InnerMeaning.sum 0 1 4 0 26%2147483647=701575401 := JFw_TX2_Head1Hi.lane4
theorem lane5 : JFv_TX2_InnerMeaning.sum 0 1 5 0 26%2147483647=413997160 := JFw_TX2_Head1Hi.lane5
theorem lane6 : JFv_TX2_InnerMeaning.sum 0 1 6 0 26%2147483647=1284607464 := JFw_TX2_Head1Hi.lane6
theorem lane7 : JFv_TX2_InnerMeaning.sum 0 1 7 0 26%2147483647=237657178 := JFw_TX2_Head1Hi.lane7
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 0 1
  have same : out=value := JFw_TX2_CellUnique.source out value (by
    intro j
    fin_cases j
    · exact (h 0).trans lane0
    · exact (h 1).trans lane1
    · exact (h 2).trans lane2
    · exact (h 3).trans lane3
    · exact (h 4).trans lane4
    · exact (h 5).trans lane5
    · exact (h 6).trans lane6
    · exact (h 7).trans lane7
    )
  exact same ▸ run
#print axioms lane0
#print axioms lane1
#print axioms lane2
#print axioms lane3
#print axioms lane4
#print axioms lane5
#print axioms lane6
#print axioms lane7
#print axioms source
end AspisR1.JFw_TX2_Head1
end
