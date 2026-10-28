import NDO_JHa_Heads1
import NDO_JHa_Tails1
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHa_Dots1
open Aeneas Aeneas.Std Result
def value0 : FIo_Install.NE := ⟨⟨⟨1104294386#u32,720857587#u32⟩,⟨966575011#u32,1698589277#u32⟩⟩,⟨⟨720244953#u32,1915033055#u32⟩,⟨634508911#u32,900318784#u32⟩⟩⟩
theorem addition0 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads1.value0 JHa_Tails1.value0=ok value0 := by
  with_unfolding_all rfl
#print axioms addition0
theorem slot0 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots1.q
    JFr_TX2_FirstLane.native 0#usize=ok value0 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots1.q JFr_TX2_FirstLane.native 0#usize=ok JHa_Tails1.value0 :=
    JHa_Tails1.source0
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads1.source0,bind_tc_ok,tail,bind_tc_ok,addition0]
#print axioms slot0
def value1 : FIo_Install.NE := ⟨⟨⟨501674758#u32,951393984#u32⟩,⟨847048177#u32,1362634893#u32⟩⟩,⟨⟨43023868#u32,1775050685#u32⟩,⟨79695355#u32,499948639#u32⟩⟩⟩
theorem addition1 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads1.value1 JHa_Tails1.value1=ok value1 := by
  with_unfolding_all rfl
#print axioms addition1
theorem slot1 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots1.q
    JFr_TX2_FirstLane.native 1#usize=ok value1 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots1.q JFr_TX2_FirstLane.native 1#usize=ok JHa_Tails1.value1 :=
    JHa_Tails1.source1
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads1.source1,bind_tc_ok,tail,bind_tc_ok,addition1]
#print axioms slot1
def value2 : FIo_Install.NE := ⟨⟨⟨2104605253#u32,1630266283#u32⟩,⟨528303231#u32,1979137618#u32⟩⟩,⟨⟨1696048404#u32,1857837136#u32⟩,⟨819312160#u32,116723867#u32⟩⟩⟩
theorem addition2 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads1.value2 JHa_Tails1.value2=ok value2 := by
  with_unfolding_all rfl
#print axioms addition2
theorem slot2 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots1.q
    JFr_TX2_FirstLane.native 2#usize=ok value2 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots1.q JFr_TX2_FirstLane.native 2#usize=ok JHa_Tails1.value2 :=
    JHa_Tails1.source2
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads1.source2,bind_tc_ok,tail,bind_tc_ok,addition2]
#print axioms slot2
def value3 : FIo_Install.NE := ⟨⟨⟨61011640#u32,2098400061#u32⟩,⟨761969375#u32,1848041763#u32⟩⟩,⟨⟨355284338#u32,1838074311#u32⟩,⟨73114254#u32,1813577200#u32⟩⟩⟩
theorem addition3 : FIo_Native.aspis_core.field.wide_exact.WideExact.add
    JHa_Heads1.value3 JHa_Tails1.value3=ok value3 := by
  with_unfolding_all rfl
#print axioms addition3
theorem slot3 : FIp_NativeDots.fast_dots.four_dots_one JGw_Dots1.q
    JFr_TX2_FirstLane.native 3#usize=ok value3 := by
  have tail : JFs_TX2_DotSuffix.tail JGw_Dots1.q JFr_TX2_FirstLane.native 3#usize=ok JHa_Tails1.value3 :=
    JHa_Tails1.source3
  rw [JFv_TX2_SlotMeaning.factor,JHa_Heads1.source3,bind_tc_ok,tail,bind_tc_ok,addition3]
#print axioms slot3
def native : Array FIo_Install.NE 4#usize := Array.make 4#usize [value0,value1,value2,value3]
def value : Array FIp_DotsAdapter.E 4#usize := FIp_DotsAdapter.fromArray native

theorem four : FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨1,by decide⟩) JFr_TX2_FirstLane.native=ok native := by
  rw [JFs_TX2_FourHead.source]
  change JFs_TX2_FourHead.slots JGw_Dots1.q JFr_TX2_FirstLane.native=ok native
  simp only [JFs_TX2_FourHead.slots,slot0,slot1,slot2,slot3,bind_tc_ok]
  rfl
#print axioms four

theorem source : JGw_Dots1.value=value := by
  have run := JGw_Dots1.source
  change (do let out ← FIp_NativeDots.fast_dots.four_dots (JFo_Opening.value ⟨1,by decide⟩) JFr_TX2_FirstLane.native
             ok (FIp_DotsAdapter.fromArray out))=ok JGw_Dots1.value at run
  rw [four,bind_tc_ok] at run
  exact (Result.ok.inj run).symm
#print axioms source
end AspisR1.JHa_Dots1
end
