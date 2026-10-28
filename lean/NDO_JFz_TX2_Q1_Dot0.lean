import NDO_JFz_TX2_Q1_Head0
import NDO_JFz_TX2_Q1_Tail0
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨894884938#u32,340004170#u32⟩,⟨2095067417#u32,814412167#u32⟩⟩,⟨⟨682888305#u32,1787566072#u32⟩,⟨824948446#u32,1388088318#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((894884938<2147483647 ∧ 340004170<2147483647) ∧ (2095067417<2147483647 ∧ 814412167<2147483647)) ∧
    ((682888305<2147483647 ∧ 1787566072<2147483647) ∧ (824948446<2147483647 ∧ 1388088318<2147483647))
  omega
theorem addition : decode JFz_TX2_Q1_Head0.value+decode JFz_TX2_Q1_Tail0.value=decode value := by
  change (⟨⟨⟨351266211,1396901370⟩,⟨1242003086,1711402560⟩⟩,⟨⟨1639470544,699071535⟩,⟨453850768,681855564⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨543618727,1090586447⟩,⟨853064331,1250493254⟩⟩,⟨⟨1190901408,1088494537⟩,⟨371097678,706232754⟩⟩⟩=⟨⟨⟨894884938,340004170⟩,⟨2095067417,814412167⟩⟩,⟨⟨682888305,1787566072⟩,⟨824948446,1388088318⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 1)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 1 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q1_Head0.value JFz_TX2_Q1_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q1_Head0.source,
      JFz_TX2_Q1_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q1_Head0.value := by
    change ((351266211<2147483647 ∧ 1396901370<2147483647) ∧ (1242003086<2147483647 ∧ 1711402560<2147483647)) ∧
      ((1639470544<2147483647 ∧ 699071535<2147483647) ∧ (453850768<2147483647 ∧ 681855564<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q1_Tail0.value := by
    change ((543618727<2147483647 ∧ 1090586447<2147483647) ∧ (853064331<2147483647 ∧ 1250493254<2147483647)) ∧
      ((1190901408<2147483647 ∧ 1088494537<2147483647) ∧ (371097678<2147483647 ∧ 706232754<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q1_Dot0
end
