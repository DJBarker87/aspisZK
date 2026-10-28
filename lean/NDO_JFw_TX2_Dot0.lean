import NDO_JFw_TX2_Head0
import NDO_JFw_TX2_Tail0
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Dot0
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1842200909#u32,1208862427#u32⟩,⟨838681037#u32,572472952#u32⟩⟩,⟨⟨541380581#u32,1864862151#u32⟩,⟨1660777595#u32,1103381136#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1842200909<2147483647 ∧ 1208862427<2147483647) ∧ (838681037<2147483647 ∧ 572472952<2147483647)) ∧
    ((541380581<2147483647 ∧ 1864862151<2147483647) ∧ (1660777595<2147483647 ∧ 1103381136<2147483647))
  omega
theorem addition : decode JFw_TX2_Head0.value+decode JFw_TX2_Tail0.value=decode value := by
  change (⟨⟨⟨894956452,1461218209⟩,⟨890010481,392624647⟩⟩,⟨⟨2005839787,672912427⟩,⟨817074034,191805019⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨947244457,1895127865⟩,⟨2096154203,179848305⟩⟩,⟨⟨683024441,1191949724⟩,⟨843703561,911576117⟩⟩⟩=⟨⟨⟨1842200909,1208862427⟩,⟨838681037,572472952⟩⟩,⟨⟨541380581,1864862151⟩,⟨1660777595,1103381136⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 0#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 0 0
  have us : Usize.ofNat (0:Fin 4).val (by have:=(0:Fin 4).isLt;scalar_tac)=0#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFw_TX2_Head0.value JFw_TX2_Tail0.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFw_TX2_Head0.source,
      JFw_TX2_Tail0.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFw_TX2_Head0.value := by
    change ((894956452<2147483647 ∧ 1461218209<2147483647) ∧ (890010481<2147483647 ∧ 392624647<2147483647)) ∧
      ((2005839787<2147483647 ∧ 672912427<2147483647) ∧ (817074034<2147483647 ∧ 191805019<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFw_TX2_Tail0.value := by
    change ((947244457<2147483647 ∧ 1895127865<2147483647) ∧ (2096154203<2147483647 ∧ 179848305<2147483647)) ∧
      ((683024441<2147483647 ∧ 1191949724<2147483647) ∧ (843703561<2147483647 ∧ 911576117<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFw_TX2_Dot0
end
