import NDO_JHa_Heads7
import NDO_JHa_Tails7
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots7
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨962069884#u32,839972696#u32⟩,⟨1725131276#u32,950599079#u32⟩⟩,⟨⟨632946433#u32,390238319#u32⟩,⟨962312768#u32,1697566241#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads7.value0 JHa_Tails7.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots7.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots7.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails7.value0 :=
    JHa_Tails7.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads7.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨1534474703#u32,67909717#u32⟩,⟨962453307#u32,1413958541#u32⟩⟩,⟨⟨2053497442#u32,867535881#u32⟩,⟨991576841#u32,344156755#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads7.value1 JHa_Tails7.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots7.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots7.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails7.value1 :=
    JHa_Tails7.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads7.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨139475372#u32,1489885560#u32⟩,⟨604296250#u32,1246975836#u32⟩⟩,⟨⟨608204704#u32,772800491#u32⟩,⟨1987217491#u32,756272758#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads7.value2 JHa_Tails7.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots7.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots7.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails7.value2 :=
    JHa_Tails7.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads7.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨671211400#u32,718779393#u32⟩,⟨690629709#u32,1345711339#u32⟩⟩,⟨⟨964523355#u32,396228866#u32⟩,⟨2142918169#u32,519326956#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads7.value3 JHa_Tails7.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots7.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots7.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails7.value3 :=
    JHa_Tails7.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads7.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨7,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots7.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots7.value=value := by
  have run := JGw_Dots7.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨7,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots7.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots7
end
