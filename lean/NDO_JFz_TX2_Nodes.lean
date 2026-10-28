import NDO_JFv_TX2_NodeCall
import NDO_JFv_TX2_Rows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Nodes
open Aeneas Aeneas.Std Result
def value0 : U32 := 639071896#u32
theorem source0 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 0).lineZ=ok value0 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 0).lineZ
  change z.val=((1254335903*1254335903%2147483647+1254335903*1254335903%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value0 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source0
def value1 : U32 := 2065007378#u32
theorem source1 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 1).lineZ=ok value1 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 1).lineZ
  change z.val=((1592160195*1592160195%2147483647+1592160195*1592160195%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value1 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source1
def value2 : U32 := 399835077#u32
theorem source2 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 2).lineZ=ok value2 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 2).lineZ
  change z.val=((1674392043*1674392043%2147483647+1674392043*1674392043%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value2 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source2
def value3 : U32 := 391651885#u32
theorem source3 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 3).lineZ=ok value3 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 3).lineZ
  change z.val=((777451883*777451883%2147483647+777451883*777451883%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value3 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source3
def value4 : U32 := 1810672442#u32
theorem source4 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 4).lineZ=ok value4 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 4).lineZ
  change z.val=((1612219610*1612219610%2147483647+1612219610*1612219610%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value4 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source4
def value5 : U32 := 2003640019#u32
theorem source5 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 5).lineZ=ok value5 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 5).lineZ
  change z.val=((1201169175*1201169175%2147483647+1201169175*1201169175%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value5 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source5
def value6 : U32 := 396914215#u32
theorem source6 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 6).lineZ=ok value6 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 6).lineZ
  change z.val=((741299484*741299484%2147483647+741299484*741299484%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value6 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source6
def value7 : U32 := 1230472626#u32
theorem source7 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 7).lineZ=ok value7 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 7).lineZ
  change z.val=((609446502*609446502%2147483647+609446502*609446502%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value7 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source7
def value8 : U32 := 580761654#u32
theorem source8 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 8).lineZ=ok value8 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 8).lineZ
  change z.val=((1978967902*1978967902%2147483647+1978967902*1978967902%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value8 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source8
def value9 : U32 := 41099316#u32
theorem source9 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 9).lineZ=ok value9 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 9).lineZ
  change z.val=((1090365005*1090365005%2147483647+1090365005*1090365005%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value9 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source9
def value10 : U32 := 541264710#u32
theorem source10 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 10).lineZ=ok value10 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 10).lineZ
  change z.val=((1121887715*1121887715%2147483647+1121887715*1121887715%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value10 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source10
def value11 : U32 := 313823750#u32
theorem source11 : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value 11).lineZ=ok value11 := by
  obtain ⟨z,run,_,hv⟩ := JFv_TX2_NodeCall.source (JFv_TX2_Rows.value 11).lineZ
  change z.val=((1773649059*1773649059%2147483647+1773649059*1773649059%2147483647)%2147483647+2147483647-1)%2147483647 at hv
  norm_num at hv
  have same : z=value11 := UScalar.eq_of_val_eq hv
  exact same ▸ run
#print axioms source11
def value (i : Fin 12) : U32 := match i.val with
  | 0 => value0
  | 1 => value1
  | 2 => value2
  | 3 => value3
  | 4 => value4
  | 5 => value5
  | 6 => value6
  | 7 => value7
  | 8 => value8
  | 9 => value9
  | 10 => value10
  | _ => value11
theorem source (i : Fin 12) : JFv_TX2_NodeCall.sourceCall (JFv_TX2_Rows.value i).lineZ=ok (value i) := by
  fin_cases i
  · exact source0
  · exact source1
  · exact source2
  · exact source3
  · exact source4
  · exact source5
  · exact source6
  · exact source7
  · exact source8
  · exact source9
  · exact source10
  · exact source11
#print axioms source
end AspisR1.JFz_TX2_Nodes
end
