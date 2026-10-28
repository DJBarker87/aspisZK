import NDO_JFw_TX2_Head00
import NDO_JFw_TX2_Head0Lo
import NDO_JFw_TX2_Head0Hi
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Head0
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨894956452#u32,1461218209#u32⟩,⟨890010481#u32,392624647#u32⟩⟩,⟨⟨2005839787#u32,672912427#u32⟩,⟨817074034#u32,191805019#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 0 0 0 0 26%2147483647=894956452 := JFw_TX2_Head00.lane0
theorem lane1 : JFv_TX2_InnerMeaning.sum 0 0 1 0 26%2147483647=1461218209 := JFw_TX2_Head0Lo.lane1
theorem lane2 : JFv_TX2_InnerMeaning.sum 0 0 2 0 26%2147483647=890010481 := JFw_TX2_Head0Lo.lane2
theorem lane3 : JFv_TX2_InnerMeaning.sum 0 0 3 0 26%2147483647=392624647 := JFw_TX2_Head0Lo.lane3
theorem lane4 : JFv_TX2_InnerMeaning.sum 0 0 4 0 26%2147483647=2005839787 := JFw_TX2_Head0Hi.lane4
theorem lane5 : JFv_TX2_InnerMeaning.sum 0 0 5 0 26%2147483647=672912427 := JFw_TX2_Head0Hi.lane5
theorem lane6 : JFv_TX2_InnerMeaning.sum 0 0 6 0 26%2147483647=817074034 := JFw_TX2_Head0Hi.lane6
theorem lane7 : JFv_TX2_InnerMeaning.sum 0 0 7 0 26%2147483647=191805019 := JFw_TX2_Head0Hi.lane7
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 0 0
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
end AspisR1.JFw_TX2_Head0
end
