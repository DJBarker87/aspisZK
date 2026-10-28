import NDO_JHa_Heads9
import NDO_JHa_Tails9
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots9
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨2091433889#u32,216499546#u32⟩,⟨646543183#u32,1305197620#u32⟩⟩,⟨⟨358695045#u32,867523287#u32⟩,⟨657368636#u32,1837953874#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads9.value0 JHa_Tails9.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots9.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots9.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails9.value0 :=
    JHa_Tails9.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads9.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨1421245089#u32,1000920033#u32⟩,⟨1221588714#u32,695708557#u32⟩⟩,⟨⟨1110421133#u32,422436494#u32⟩,⟨1188534145#u32,525893899#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads9.value1 JHa_Tails9.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots9.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots9.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails9.value1 :=
    JHa_Tails9.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads9.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨2072349020#u32,1219848130#u32⟩,⟨1719168583#u32,928845083#u32⟩⟩,⟨⟨142017361#u32,1012092072#u32⟩,⟨2049535405#u32,1268482942#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads9.value2 JHa_Tails9.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots9.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots9.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails9.value2 :=
    JHa_Tails9.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads9.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨111802728#u32,849729340#u32⟩,⟨2109353476#u32,705915247#u32⟩⟩,⟨⟨770158786#u32,638923881#u32⟩,⟨564073464#u32,973676869#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads9.value3 JHa_Tails9.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots9.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots9.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails9.value3 :=
    JHa_Tails9.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads9.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨9,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots9.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots9.value=value := by
  have run := JGw_Dots9.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨9,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots9.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots9
end
