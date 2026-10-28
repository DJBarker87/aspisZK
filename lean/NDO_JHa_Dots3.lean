import NDO_JHa_Heads3
import NDO_JHa_Tails3
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots3
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨1378643633#u32,1998300647#u32⟩,⟨1303355456#u32,504658715#u32⟩⟩,⟨⟨1395440008#u32,844315861#u32⟩,⟨1494641892#u32,1110651981#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads3.value0 JHa_Tails3.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots3.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots3.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails3.value0 :=
    JHa_Tails3.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads3.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨672286286#u32,1432112492#u32⟩,⟨771518612#u32,1902903684#u32⟩⟩,⟨⟨2022515589#u32,216190726#u32⟩,⟨977464792#u32,559433199#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads3.value1 JHa_Tails3.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots3.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots3.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails3.value1 :=
    JHa_Tails3.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads3.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨1700966359#u32,677121751#u32⟩,⟨1717157459#u32,1551021537#u32⟩⟩,⟨⟨1850621594#u32,1189514123#u32⟩,⟨1824633388#u32,1447799076#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads3.value2 JHa_Tails3.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots3.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots3.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails3.value2 :=
    JHa_Tails3.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads3.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨1039367122#u32,225930383#u32⟩,⟨788194480#u32,1728281297#u32⟩⟩,⟨⟨1325536372#u32,248707082#u32⟩,⟨1886287452#u32,19462060#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads3.value3 JHa_Tails3.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots3.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots3.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails3.value3 :=
    JHa_Tails3.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads3.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨3,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots3.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots3.value=value := by
  have run := JGw_Dots3.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨3,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots3.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots3
end
