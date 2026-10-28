import NDO_JHa_Heads4
import NDO_JHa_Tails4
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots4
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨248068782#u32,875494695#u32⟩,⟨1255231373#u32,1306862877#u32⟩⟩,⟨⟨2136045275#u32,1239930110#u32⟩,⟨224918844#u32,2017869355#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads4.value0 JHa_Tails4.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots4.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots4.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails4.value0 :=
    JHa_Tails4.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads4.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨988444794#u32,337131938#u32⟩,⟨511489315#u32,860404759#u32⟩⟩,⟨⟨1451223432#u32,1658110460#u32⟩,⟨256252699#u32,1358443403#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads4.value1 JHa_Tails4.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots4.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots4.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails4.value1 :=
    JHa_Tails4.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads4.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨843289301#u32,377020022#u32⟩,⟨2071691786#u32,592886191#u32⟩⟩,⟨⟨2049772026#u32,1564388390#u32⟩,⟨1687722914#u32,855145008#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads4.value2 JHa_Tails4.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots4.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots4.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails4.value2 :=
    JHa_Tails4.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads4.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨2113159715#u32,186146095#u32⟩,⟨967043042#u32,1468499884#u32⟩⟩,⟨⟨928817204#u32,369628456#u32⟩,⟨1866374177#u32,1401564895#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads4.value3 JHa_Tails4.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots4.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots4.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails4.value3 :=
    JHa_Tails4.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads4.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨4,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots4.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots4.value=value := by
  have run := JGw_Dots4.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨4,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots4.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots4
end
