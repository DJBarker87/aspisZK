import NDO_JHu_DigestTransport
import NDO_NCV_FieldViews
import NDO_JHg_AccountValues
import NDO_JHg_Digest00
import NDO_JHg_Digest01
import NDO_JHg_Digest02
import NDO_JHg_Digest03
import NDO_JHg_Digest04
import NDO_JHg_Digest05
import NDO_JHg_Digest06
import NDO_JHg_Digest07
import NDO_JHg_Digest08
import NDO_JHg_Digest09
import NDO_JHg_Digest10
import NDO_JHg_Digest11
import NDO_JHg_Digest12
import NDO_JHg_Digest13
import NDO_JHg_Digest14
import NDO_JHg_Digest15
import NDO_JHg_Digest16
import NDO_JHg_Digest17
import NDO_JHg_Digest18
import NDO_JHg_Digest19
import NDO_JHg_Digest20
import NDO_JHg_Digest21
set_option autoImplicit false
namespace AspisR1.JHu_FixtureDigests
open Aeneas Aeneas.Std Result AspisR1

def tree : Slice U8 := JHg_FieldRead.segment JHb_DataLane.value 80 688

theorem tree_length : tree.val.length=688 := by
  apply JHg_FieldRead.length
  have h : JHb_DataLane.value.val.length=768 := JHb_DataLane.length
  omega

theorem checkpoint : NCV_Reference.digest JHg_DataForest.value 80#usize=ok (.Ok JFt_Digest00.value) := by
  have len : JHg_DataForest.value.val.length=192 := JHg_DataForest.length
  exact JHu_DigestTransport.source _ _ _ (by omega) (by scalar_tac) JHg_Digest00.source

theorem lane_root : NCV_Reference.digest tree 16#usize=ok (.Ok JFt_Digest01.value) := by
  have same : JHg_FieldRead.segment tree (16#usize).val 32=JHg_Digest01.window := by
    rw [show (16#usize).val=16 from rfl]
    unfold tree JHg_Digest01.window
    exact NCV_FieldViews.nested _ 80 688 16 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest01.source

theorem frontier_00 : NCV_Reference.digest tree 48#usize=ok (.Ok JFt_Digest02.value) := by
  have same : JHg_FieldRead.segment tree (48#usize).val 32=JHg_Digest02.window := by
    rw [show (48#usize).val=48 from rfl]
    unfold tree JHg_Digest02.window
    exact NCV_FieldViews.nested _ 80 688 48 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest02.source

theorem frontier_01 : NCV_Reference.digest tree 80#usize=ok (.Ok JFt_Digest03.value) := by
  have same : JHg_FieldRead.segment tree (80#usize).val 32=JHg_Digest03.window := by
    rw [show (80#usize).val=80 from rfl]
    unfold tree JHg_Digest03.window
    exact NCV_FieldViews.nested _ 80 688 80 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest03.source

theorem frontier_02 : NCV_Reference.digest tree 112#usize=ok (.Ok JFt_Digest04.value) := by
  have same : JHg_FieldRead.segment tree (112#usize).val 32=JHg_Digest04.window := by
    rw [show (112#usize).val=112 from rfl]
    unfold tree JHg_Digest04.window
    exact NCV_FieldViews.nested _ 80 688 112 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest04.source

theorem frontier_03 : NCV_Reference.digest tree 144#usize=ok (.Ok JFt_Digest05.value) := by
  have same : JHg_FieldRead.segment tree (144#usize).val 32=JHg_Digest05.window := by
    rw [show (144#usize).val=144 from rfl]
    unfold tree JHg_Digest05.window
    exact NCV_FieldViews.nested _ 80 688 144 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest05.source

theorem frontier_04 : NCV_Reference.digest tree 176#usize=ok (.Ok JFt_Digest06.value) := by
  have same : JHg_FieldRead.segment tree (176#usize).val 32=JHg_Digest06.window := by
    rw [show (176#usize).val=176 from rfl]
    unfold tree JHg_Digest06.window
    exact NCV_FieldViews.nested _ 80 688 176 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest06.source

theorem frontier_05 : NCV_Reference.digest tree 208#usize=ok (.Ok JFt_Digest07.value) := by
  have same : JHg_FieldRead.segment tree (208#usize).val 32=JHg_Digest07.window := by
    rw [show (208#usize).val=208 from rfl]
    unfold tree JHg_Digest07.window
    exact NCV_FieldViews.nested _ 80 688 208 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest07.source

theorem frontier_06 : NCV_Reference.digest tree 240#usize=ok (.Ok JFt_Digest08.value) := by
  have same : JHg_FieldRead.segment tree (240#usize).val 32=JHg_Digest08.window := by
    rw [show (240#usize).val=240 from rfl]
    unfold tree JHg_Digest08.window
    exact NCV_FieldViews.nested _ 80 688 240 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest08.source

theorem frontier_07 : NCV_Reference.digest tree 272#usize=ok (.Ok JFt_Digest09.value) := by
  have same : JHg_FieldRead.segment tree (272#usize).val 32=JHg_Digest09.window := by
    rw [show (272#usize).val=272 from rfl]
    unfold tree JHg_Digest09.window
    exact NCV_FieldViews.nested _ 80 688 272 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest09.source

theorem frontier_08 : NCV_Reference.digest tree 304#usize=ok (.Ok JFt_Digest10.value) := by
  have same : JHg_FieldRead.segment tree (304#usize).val 32=JHg_Digest10.window := by
    rw [show (304#usize).val=304 from rfl]
    unfold tree JHg_Digest10.window
    exact NCV_FieldViews.nested _ 80 688 304 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest10.source

theorem frontier_09 : NCV_Reference.digest tree 336#usize=ok (.Ok JFt_Digest11.value) := by
  have same : JHg_FieldRead.segment tree (336#usize).val 32=JHg_Digest11.window := by
    rw [show (336#usize).val=336 from rfl]
    unfold tree JHg_Digest11.window
    exact NCV_FieldViews.nested _ 80 688 336 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest11.source

theorem frontier_10 : NCV_Reference.digest tree 368#usize=ok (.Ok JFt_Digest12.value) := by
  have same : JHg_FieldRead.segment tree (368#usize).val 32=JHg_Digest12.window := by
    rw [show (368#usize).val=368 from rfl]
    unfold tree JHg_Digest12.window
    exact NCV_FieldViews.nested _ 80 688 368 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest12.source

theorem frontier_11 : NCV_Reference.digest tree 400#usize=ok (.Ok JFt_Digest13.value) := by
  have same : JHg_FieldRead.segment tree (400#usize).val 32=JHg_Digest13.window := by
    rw [show (400#usize).val=400 from rfl]
    unfold tree JHg_Digest13.window
    exact NCV_FieldViews.nested _ 80 688 400 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest13.source

theorem frontier_12 : NCV_Reference.digest tree 432#usize=ok (.Ok JFt_Digest14.value) := by
  have same : JHg_FieldRead.segment tree (432#usize).val 32=JHg_Digest14.window := by
    rw [show (432#usize).val=432 from rfl]
    unfold tree JHg_Digest14.window
    exact NCV_FieldViews.nested _ 80 688 432 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest14.source

theorem frontier_13 : NCV_Reference.digest tree 464#usize=ok (.Ok JFt_Digest15.value) := by
  have same : JHg_FieldRead.segment tree (464#usize).val 32=JHg_Digest15.window := by
    rw [show (464#usize).val=464 from rfl]
    unfold tree JHg_Digest15.window
    exact NCV_FieldViews.nested _ 80 688 464 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest15.source

theorem frontier_14 : NCV_Reference.digest tree 496#usize=ok (.Ok JFt_Digest16.value) := by
  have same : JHg_FieldRead.segment tree (496#usize).val 32=JHg_Digest16.window := by
    rw [show (496#usize).val=496 from rfl]
    unfold tree JHg_Digest16.window
    exact NCV_FieldViews.nested _ 80 688 496 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest16.source

theorem frontier_15 : NCV_Reference.digest tree 528#usize=ok (.Ok JFt_Digest17.value) := by
  have same : JHg_FieldRead.segment tree (528#usize).val 32=JHg_Digest17.window := by
    rw [show (528#usize).val=528 from rfl]
    unfold tree JHg_Digest17.window
    exact NCV_FieldViews.nested _ 80 688 528 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest17.source

theorem frontier_16 : NCV_Reference.digest tree 560#usize=ok (.Ok JFt_Digest18.value) := by
  have same : JHg_FieldRead.segment tree (560#usize).val 32=JHg_Digest18.window := by
    rw [show (560#usize).val=560 from rfl]
    unfold tree JHg_Digest18.window
    exact NCV_FieldViews.nested _ 80 688 560 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest18.source

theorem frontier_17 : NCV_Reference.digest tree 592#usize=ok (.Ok JFt_Digest19.value) := by
  have same : JHg_FieldRead.segment tree (592#usize).val 32=JHg_Digest19.window := by
    rw [show (592#usize).val=592 from rfl]
    unfold tree JHg_Digest19.window
    exact NCV_FieldViews.nested _ 80 688 592 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest19.source

theorem frontier_18 : NCV_Reference.digest tree 624#usize=ok (.Ok JFt_Digest20.value) := by
  have same : JHg_FieldRead.segment tree (624#usize).val 32=JHg_Digest20.window := by
    rw [show (624#usize).val=624 from rfl]
    unfold tree JHg_Digest20.window
    exact NCV_FieldViews.nested _ 80 688 624 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest20.source

theorem frontier_19 : NCV_Reference.digest tree 656#usize=ok (.Ok JFt_Digest21.value) := by
  have same : JHg_FieldRead.segment tree (656#usize).val 32=JHg_Digest21.window := by
    rw [show (656#usize).val=656 from rfl]
    unfold tree JHg_Digest21.window
    exact NCV_FieldViews.nested _ 80 688 656 32 (by omega)
  apply JHu_DigestTransport.source _ _ _ (by rw [tree_length];omega) (by rw [tree_length];scalar_tac)
  rw [same]
  exact JHg_Digest21.source

#print axioms tree_length
#print axioms checkpoint
#print axioms lane_root
#print axioms frontier_00
#print axioms frontier_01
#print axioms frontier_02
#print axioms frontier_03
#print axioms frontier_04
#print axioms frontier_05
#print axioms frontier_06
#print axioms frontier_07
#print axioms frontier_08
#print axioms frontier_09
#print axioms frontier_10
#print axioms frontier_11
#print axioms frontier_12
#print axioms frontier_13
#print axioms frontier_14
#print axioms frontier_15
#print axioms frontier_16
#print axioms frontier_17
#print axioms frontier_18
#print axioms frontier_19
end AspisR1.JHu_FixtureDigests
