import NDO_JFw_TX2_Head2
import NDO_JFw_TX2_Tail2
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1347065123#u32,438591365#u32⟩,⟨1284475829#u32,1677210292#u32⟩⟩,⟨⟨1472717172#u32,2099714719#u32⟩,⟨1572697310#u32,1548192378#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1347065123<2147483647 ∧ 438591365<2147483647) ∧ (1284475829<2147483647 ∧ 1677210292<2147483647)) ∧
    ((1472717172<2147483647 ∧ 2099714719<2147483647) ∧ (1572697310<2147483647 ∧ 1548192378<2147483647))
  omega
theorem addition : decode JFw_TX2_Head2.value+decode JFw_TX2_Tail2.value=decode value := by
  change (⟨⟨⟨144768424,287969585⟩,⟨769028145,285797922⟩⟩,⟨⟨1923381507,1280053809⟩,⟨844596158,302332130⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1202296699,150621780⟩,⟨515447684,1391412370⟩⟩,⟨⟨1696819312,819660910⟩,⟨728101152,1245860248⟩⟩⟩=⟨⟨⟨1347065123,438591365⟩,⟨1284475829,1677210292⟩⟩,⟨⟨1472717172,2099714719⟩,⟨1572697310,1548192378⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 0 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFw_TX2_Head2.value JFw_TX2_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFw_TX2_Head2.source,
      JFw_TX2_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFw_TX2_Head2.value := by
    change ((144768424<2147483647 ∧ 287969585<2147483647) ∧ (769028145<2147483647 ∧ 285797922<2147483647)) ∧
      ((1923381507<2147483647 ∧ 1280053809<2147483647) ∧ (844596158<2147483647 ∧ 302332130<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFw_TX2_Tail2.value := by
    change ((1202296699<2147483647 ∧ 150621780<2147483647) ∧ (515447684<2147483647 ∧ 1391412370<2147483647)) ∧
      ((1696819312<2147483647 ∧ 819660910<2147483647) ∧ (728101152<2147483647 ∧ 1245860248<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFw_TX2_Dot2
end
