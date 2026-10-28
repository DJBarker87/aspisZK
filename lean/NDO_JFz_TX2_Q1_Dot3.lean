import NDO_JFz_TX2_Q1_Head3
import NDO_JFz_TX2_Q1_Tail3
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨191987829#u32,1092071520#u32⟩,⟨673054054#u32,1469558453#u32⟩⟩,⟨⟨1564945648#u32,1807264378#u32⟩,⟨504831538#u32,1510763137#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((191987829<2147483647 ∧ 1092071520<2147483647) ∧ (673054054<2147483647 ∧ 1469558453<2147483647)) ∧
    ((1564945648<2147483647 ∧ 1807264378<2147483647) ∧ (504831538<2147483647 ∧ 1510763137<2147483647))
  omega
theorem addition : decode JFz_TX2_Q1_Head3.value+decode JFz_TX2_Q1_Tail3.value=decode value := by
  change (⟨⟨⟨939241924,1461960841⟩,⟨1051838937,1279776080⟩⟩,⟨⟨190154997,1044345489⟩,⟨680538147,1549513923⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1400229552,1777594326⟩,⟨1768698764,189782373⟩⟩,⟨⟨1374790651,762918889⟩,⟨1971777038,2108732861⟩⟩⟩=⟨⟨⟨191987829,1092071520⟩,⟨673054054,1469558453⟩⟩,⟨⟨1564945648,1807264378⟩,⟨504831538,1510763137⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 1)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 1 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q1_Head3.value JFz_TX2_Q1_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q1_Head3.source,
      JFz_TX2_Q1_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q1_Head3.value := by
    change ((939241924<2147483647 ∧ 1461960841<2147483647) ∧ (1051838937<2147483647 ∧ 1279776080<2147483647)) ∧
      ((190154997<2147483647 ∧ 1044345489<2147483647) ∧ (680538147<2147483647 ∧ 1549513923<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q1_Tail3.value := by
    change ((1400229552<2147483647 ∧ 1777594326<2147483647) ∧ (1768698764<2147483647 ∧ 189782373<2147483647)) ∧
      ((1374790651<2147483647 ∧ 762918889<2147483647) ∧ (1971777038<2147483647 ∧ 2108732861<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q1_Dot3
end
