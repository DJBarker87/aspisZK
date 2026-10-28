import NDO_JHa_Heads6
import NDO_JHa_Tails6
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots6
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨340496462#u32,927013527#u32⟩,⟨409577040#u32,1265424778#u32⟩⟩,⟨⟨1024733769#u32,1837115435#u32⟩,⟨1347457310#u32,103842217#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads6.value0 JHa_Tails6.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots6.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots6.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails6.value0 :=
    JHa_Tails6.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads6.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨355291408#u32,515929680#u32⟩,⟨1611022204#u32,329031969#u32⟩⟩,⟨⟨1088386878#u32,339553167#u32⟩,⟨1007157258#u32,1125622910#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads6.value1 JHa_Tails6.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots6.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots6.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails6.value1 :=
    JHa_Tails6.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads6.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨726189189#u32,1954132106#u32⟩,⟨508877039#u32,1796746750#u32⟩⟩,⟨⟨561074169#u32,618403246#u32⟩,⟨1333634584#u32,1116054999#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads6.value2 JHa_Tails6.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots6.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots6.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails6.value2 :=
    JHa_Tails6.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads6.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨805921010#u32,2062445053#u32⟩,⟨143859067#u32,172583582#u32⟩⟩,⟨⟨2116157181#u32,1482395408#u32⟩,⟨99914322#u32,182710739#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads6.value3 JHa_Tails6.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots6.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots6.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails6.value3 :=
    JHa_Tails6.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads6.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨6,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots6.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots6.value=value := by
  have run := JGw_Dots6.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨6,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots6.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots6
end
