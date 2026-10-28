import NDO_JFw_TX2_Head3
import NDO_JFw_TX2_Tail3
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Dot3
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨742323479#u32,1312972604#u32⟩,⟨1244769140#u32,478125974#u32⟩⟩,⟨⟨1329886131#u32,605025761#u32⟩,⟨692692841#u32,1013742790#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((742323479<2147483647 ∧ 1312972604<2147483647) ∧ (1244769140<2147483647 ∧ 478125974<2147483647)) ∧
    ((1329886131<2147483647 ∧ 605025761<2147483647) ∧ (692692841<2147483647 ∧ 1013742790<2147483647))
  omega
theorem addition : decode JFw_TX2_Head3.value+decode JFw_TX2_Tail3.value=decode value := by
  change (⟨⟨⟨915385587,1608512048⟩,⟨644797708,1160228903⟩⟩,⟨⟨457751545,599609738⟩,⟨787010880,2138175076⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1974421539,1851944203⟩,⟨599971432,1465380718⟩⟩,⟨⟨872134586,5416023⟩,⟨2053165608,1023051361⟩⟩⟩=⟨⟨⟨742323479,1312972604⟩,⟨1244769140,478125974⟩⟩,⟨⟨1329886131,605025761⟩,⟨692692841,1013742790⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 3#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 0 3
  have us : Usize.ofNat (3:Fin 4).val (by have:=(3:Fin 4).isLt;scalar_tac)=3#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFw_TX2_Head3.value JFw_TX2_Tail3.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFw_TX2_Head3.source,
      JFw_TX2_Tail3.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFw_TX2_Head3.value := by
    change ((915385587<2147483647 ∧ 1608512048<2147483647) ∧ (644797708<2147483647 ∧ 1160228903<2147483647)) ∧
      ((457751545<2147483647 ∧ 599609738<2147483647) ∧ (787010880<2147483647 ∧ 2138175076<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFw_TX2_Tail3.value := by
    change ((1974421539<2147483647 ∧ 1851944203<2147483647) ∧ (599971432<2147483647 ∧ 1465380718<2147483647)) ∧
      ((872134586<2147483647 ∧ 5416023<2147483647) ∧ (2053165608<2147483647 ∧ 1023051361<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFw_TX2_Dot3
end
