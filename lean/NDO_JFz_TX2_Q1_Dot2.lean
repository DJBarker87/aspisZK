import NDO_JFz_TX2_Q1_Head2
import NDO_JFz_TX2_Q1_Tail2
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Dot2
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1544647403#u32,770657119#u32⟩,⟨1803516558#u32,703409563#u32⟩⟩,⟨⟨302326034#u32,823575564#u32⟩,⟨890239946#u32,651590771#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1544647403<2147483647 ∧ 770657119<2147483647) ∧ (1803516558<2147483647 ∧ 703409563<2147483647)) ∧
    ((302326034<2147483647 ∧ 823575564<2147483647) ∧ (890239946<2147483647 ∧ 651590771<2147483647))
  omega
theorem addition : decode JFz_TX2_Q1_Head2.value+decode JFz_TX2_Q1_Tail2.value=decode value := by
  change (⟨⟨⟨846099081,858420302⟩,⟨669654871,753966456⟩⟩,⟨⟨1094838863,657863607⟩,⟨320985659,1524915235⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨698548322,2059720464⟩,⟨1133861687,2096926754⟩⟩,⟨⟨1354970818,165711957⟩,⟨569254287,1274159183⟩⟩⟩=⟨⟨⟨1544647403,770657119⟩,⟨1803516558,703409563⟩⟩,⟨⟨302326034,823575564⟩,⟨890239946,651590771⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 1)) JFr_TX2_FirstLane.native 2#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 1 2
  have us : Usize.ofNat (2:Fin 4).val (by have:=(2:Fin 4).isLt;scalar_tac)=2#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q1_Head2.value JFz_TX2_Q1_Tail2.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q1_Head2.source,
      JFz_TX2_Q1_Tail2.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q1_Head2.value := by
    change ((846099081<2147483647 ∧ 858420302<2147483647) ∧ (669654871<2147483647 ∧ 753966456<2147483647)) ∧
      ((1094838863<2147483647 ∧ 657863607<2147483647) ∧ (320985659<2147483647 ∧ 1524915235<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q1_Tail2.value := by
    change ((698548322<2147483647 ∧ 2059720464<2147483647) ∧ (1133861687<2147483647 ∧ 2096926754<2147483647)) ∧
      ((1354970818<2147483647 ∧ 165711957<2147483647) ∧ (569254287<2147483647 ∧ 1274159183<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q1_Dot2
end
