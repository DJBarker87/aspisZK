import NDO_JFw_TX2_Head3Lo
import NDO_JFw_TX2_Head3Hi
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Head3
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨915385587#u32,1608512048#u32⟩,⟨644797708#u32,1160228903#u32⟩⟩,⟨⟨457751545#u32,599609738#u32⟩,⟨787010880#u32,2138175076#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 0 3 0 0 26%2147483647=915385587 := JFw_TX2_Head3Lo.lane0
theorem lane1 : JFv_TX2_InnerMeaning.sum 0 3 1 0 26%2147483647=1608512048 := JFw_TX2_Head3Lo.lane1
theorem lane2 : JFv_TX2_InnerMeaning.sum 0 3 2 0 26%2147483647=644797708 := JFw_TX2_Head3Lo.lane2
theorem lane3 : JFv_TX2_InnerMeaning.sum 0 3 3 0 26%2147483647=1160228903 := JFw_TX2_Head3Lo.lane3
theorem lane4 : JFv_TX2_InnerMeaning.sum 0 3 4 0 26%2147483647=457751545 := JFw_TX2_Head3Hi.lane4
theorem lane5 : JFv_TX2_InnerMeaning.sum 0 3 5 0 26%2147483647=599609738 := JFw_TX2_Head3Hi.lane5
theorem lane6 : JFv_TX2_InnerMeaning.sum 0 3 6 0 26%2147483647=787010880 := JFw_TX2_Head3Hi.lane6
theorem lane7 : JFv_TX2_InnerMeaning.sum 0 3 7 0 26%2147483647=2138175076 := JFw_TX2_Head3Hi.lane7
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 0 3
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
end AspisR1.JFw_TX2_Head3
end
