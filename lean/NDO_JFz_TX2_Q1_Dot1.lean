import NDO_JFz_TX2_Q1_Head1
import NDO_JFz_TX2_Q1_Tail1
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFz_TX2_Q1_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨2019115892#u32,1269435012#u32⟩,⟨2110199430#u32,696508351#u32⟩⟩,⟨⟨1575409362#u32,886082674#u32⟩,⟨837000337#u32,743698602#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((2019115892<2147483647 ∧ 1269435012<2147483647) ∧ (2110199430<2147483647 ∧ 696508351<2147483647)) ∧
    ((1575409362<2147483647 ∧ 886082674<2147483647) ∧ (837000337<2147483647 ∧ 743698602<2147483647))
  omega
theorem addition : decode JFz_TX2_Q1_Head1.value+decode JFz_TX2_Q1_Tail1.value=decode value := by
  change (⟨⟨⟨1175496257,1673275703⟩,⟨2075443034,497949967⟩⟩,⟨⟨1084853583,1411731643⟩,⟨1286994389,307109789⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨843619635,1743642956⟩,⟨34756396,198558384⟩⟩,⟨⟨490555779,1621834678⟩,⟨1697489595,436588813⟩⟩⟩=⟨⟨⟨2019115892,1269435012⟩,⟨2110199430,696508351⟩⟩,⟨⟨1575409362,886082674⟩,⟨837000337,743698602⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 1)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 1 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFz_TX2_Q1_Head1.value JFz_TX2_Q1_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFz_TX2_Q1_Head1.source,
      JFz_TX2_Q1_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFz_TX2_Q1_Head1.value := by
    change ((1175496257<2147483647 ∧ 1673275703<2147483647) ∧ (2075443034<2147483647 ∧ 497949967<2147483647)) ∧
      ((1084853583<2147483647 ∧ 1411731643<2147483647) ∧ (1286994389<2147483647 ∧ 307109789<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFz_TX2_Q1_Tail1.value := by
    change ((843619635<2147483647 ∧ 1743642956<2147483647) ∧ (34756396<2147483647 ∧ 198558384<2147483647)) ∧
      ((490555779<2147483647 ∧ 1621834678<2147483647) ∧ (1697489595<2147483647 ∧ 436588813<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFz_TX2_Q1_Dot1
end
