import NDO_JHa_Heads5
import NDO_JHa_Tails5
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots5
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨889701891#u32,1831850509#u32⟩,⟨1984792026#u32,1468090803#u32⟩⟩,⟨⟨831003424#u32,582650226#u32⟩,⟨630659388#u32,468889793#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads5.value0 JHa_Tails5.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots5.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots5.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails5.value0 :=
    JHa_Tails5.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads5.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨1782986818#u32,634368823#u32⟩,⟨1026224551#u32,13815773#u32⟩⟩,⟨⟨825477512#u32,608692736#u32⟩,⟨1664668134#u32,1312633504#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads5.value1 JHa_Tails5.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots5.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots5.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails5.value1 :=
    JHa_Tails5.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads5.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨1671330790#u32,242136476#u32⟩,⟨481917149#u32,1289523696#u32⟩⟩,⟨⟨1583721934#u32,134400336#u32⟩,⟨744502957#u32,1192325426#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads5.value2 JHa_Tails5.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots5.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots5.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails5.value2 :=
    JHa_Tails5.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads5.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨603360479#u32,1766339871#u32⟩,⟨460737010#u32,787745691#u32⟩⟩,⟨⟨613568246#u32,1473058914#u32⟩,⟨1026134876#u32,417493778#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads5.value3 JHa_Tails5.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots5.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots5.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails5.value3 :=
    JHa_Tails5.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads5.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨5,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots5.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots5.value=value := by
  have run := JGw_Dots5.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨5,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots5.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots5
end
