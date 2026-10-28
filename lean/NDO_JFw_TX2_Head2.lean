import NDO_JFw_TX2_Head2Lo
import NDO_JFw_TX2_Head2Hi
import NDO_JFw_TX2_Coefficients
import NDO_JFw_TX2_CellUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Head2
open Aeneas Aeneas.Std Result
open JFv_TX2_ArrayMeaning (cell)
def value : FIo_Install.NE := ⟨⟨⟨144768424#u32,287969585#u32⟩,⟨769028145#u32,285797922#u32⟩⟩,⟨⟨1923381507#u32,1280053809#u32⟩,⟨844596158#u32,302332130#u32⟩⟩⟩
theorem lane0 : JFv_TX2_InnerMeaning.sum 0 2 0 0 26%2147483647=144768424 := JFw_TX2_Head2Lo.lane0
theorem lane1 : JFv_TX2_InnerMeaning.sum 0 2 1 0 26%2147483647=287969585 := JFw_TX2_Head2Lo.lane1
theorem lane2 : JFv_TX2_InnerMeaning.sum 0 2 2 0 26%2147483647=769028145 := JFw_TX2_Head2Lo.lane2
theorem lane3 : JFv_TX2_InnerMeaning.sum 0 2 3 0 26%2147483647=285797922 := JFw_TX2_Head2Lo.lane3
theorem lane4 : JFv_TX2_InnerMeaning.sum 0 2 4 0 26%2147483647=1923381507 := JFw_TX2_Head2Hi.lane4
theorem lane5 : JFv_TX2_InnerMeaning.sum 0 2 5 0 26%2147483647=1280053809 := JFw_TX2_Head2Hi.lane5
theorem lane6 : JFv_TX2_InnerMeaning.sum 0 2 6 0 26%2147483647=844596158 := JFw_TX2_Head2Hi.lane6
theorem lane7 : JFv_TX2_InnerMeaning.sum 0 2 7 0 26%2147483647=302332130 := JFw_TX2_Head2Hi.lane7
theorem source : JFs_TX2_ScalarHead.sourceCall
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,_,h⟩ := JFv_TX2_HeadFlat.source 0 2
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
end AspisR1.JFw_TX2_Head2
end
