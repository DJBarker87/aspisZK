import NDO_JHa_Heads2
import NDO_JHa_Tails2
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots2
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨96581048#u32,1544788512#u32⟩,⟨2015746449#u32,292679947#u32⟩⟩,⟨⟨177113647#u32,666820863#u32⟩,⟨1428735792#u32,2082279749#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads2.value0 JHa_Tails2.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots2.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots2.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails2.value0 :=
    JHa_Tails2.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads2.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨1227710331#u32,1387729318#u32⟩,⟨1827069504#u32,845580921#u32⟩⟩,⟨⟨524622376#u32,1286669910#u32⟩,⟨1485867935#u32,550658571#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads2.value1 JHa_Tails2.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots2.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots2.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails2.value1 :=
    JHa_Tails2.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads2.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨1612640045#u32,83763139#u32⟩,⟨1492546388#u32,1326071024#u32⟩⟩,⟨⟨693208606#u32,1306601584#u32⟩,⟨990664624#u32,1795172001#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads2.value2 JHa_Tails2.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots2.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots2.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails2.value2 :=
    JHa_Tails2.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads2.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨1563073245#u32,1758285753#u32⟩,⟨1505530329#u32,1462669384#u32⟩⟩,⟨⟨1185886482#u32,57327564#u32⟩,⟨186988759#u32,702385730#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads2.value3 JHa_Tails2.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots2.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots2.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails2.value3 :=
    JHa_Tails2.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads2.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨2,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots2.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots2.value=value := by
  have run := JGw_Dots2.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨2,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots2.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots2
end
