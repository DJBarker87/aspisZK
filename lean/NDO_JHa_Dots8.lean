import NDO_JHa_Heads8
import NDO_JHa_Tails8
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots8
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨785136080#u32,1119168087#u32⟩,⟨828182209#u32,255954801#u32⟩⟩,⟨⟨576478090#u32,1008883790#u32⟩,⟨2109828463#u32,346997716#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads8.value0 JHa_Tails8.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots8.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots8.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails8.value0 :=
    JHa_Tails8.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads8.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨346389291#u32,822587058#u32⟩,⟨1654116951#u32,451444269#u32⟩⟩,⟨⟨919675880#u32,250077772#u32⟩,⟨1308804866#u32,1040159619#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads8.value1 JHa_Tails8.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots8.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots8.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails8.value1 :=
    JHa_Tails8.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads8.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨1654106065#u32,918901178#u32⟩,⟨146561791#u32,415977228#u32⟩⟩,⟨⟨1966525320#u32,140857527#u32⟩,⟨1839272516#u32,1866181757#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads8.value2 JHa_Tails8.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots8.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots8.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails8.value2 :=
    JHa_Tails8.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads8.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨425640799#u32,566729494#u32⟩,⟨703618548#u32,635859370#u32⟩⟩,⟨⟨157669417#u32,1537585257#u32⟩,⟨491720510#u32,1945276309#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads8.value3 JHa_Tails8.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots8.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots8.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails8.value3 :=
    JHa_Tails8.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads8.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨8,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots8.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots8.value=value := by
  have run := JGw_Dots8.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨8,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots8.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots8
end
