import NDO_JHa_Heads0
import NDO_JHa_Tails0
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots0
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨104132695#u32,1651415809#u32⟩,⟨507121032#u32,221042496#u32⟩⟩,⟨⟨1130441#u32,1178487768#u32⟩,⟨154802184#u32,64723860#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads0.value0 JHa_Tails0.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots0.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots0.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails0.value0 :=
    JHa_Tails0.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads0.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨2045764542#u32,548531564#u32⟩,⟨1467598750#u32,257544154#u32⟩⟩,⟨⟨1102161475#u32,1010421797#u32⟩,⟨620633619#u32,947414456#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads0.value1 JHa_Tails0.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots0.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots0.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails0.value1 :=
    JHa_Tails0.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads0.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨213701450#u32,1562527507#u32⟩,⟨1451282042#u32,277176222#u32⟩⟩,⟨⟨521945569#u32,1460882455#u32⟩,⟨1293777146#u32,1767770813#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads0.value2 JHa_Tails0.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots0.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots0.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails0.value2 :=
    JHa_Tails0.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads0.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨1735811452#u32,1683257143#u32⟩,⟨1314158318#u32,208881243#u32⟩⟩,⟨⟨606692581#u32,1217225111#u32⟩,⟨836731196#u32,1888388221#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads0.value3 JHa_Tails0.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots0.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots0.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails0.value3 :=
    JHa_Tails0.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads0.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨0,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots0.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots0.value=value := by
  have run := JGw_Dots0.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨0,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots0.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots0
end
