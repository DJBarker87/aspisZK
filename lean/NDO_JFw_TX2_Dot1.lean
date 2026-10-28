import NDO_JFw_TX2_Head1
import NDO_JFw_TX2_Tail1
import NDO_JFv_TX2_SlotMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_Dot1
open Aeneas Aeneas.Std Result
open JFw_TX2_PowersExplicit (decode)
def value : FIo_Install.NE := ⟨⟨⟨1594855972#u32,58894088#u32⟩,⟨578797813#u32,626740424#u32⟩⟩,⟨⟨1574036973#u32,1804222405#u32⟩,⟨938683893#u32,984465438#u32⟩⟩⟩
theorem canonical : FIo_WideValues.Canon value := by
  change ((1594855972<2147483647 ∧ 58894088<2147483647) ∧ (578797813<2147483647 ∧ 626740424<2147483647)) ∧
    ((1574036973<2147483647 ∧ 1804222405<2147483647) ∧ (938683893<2147483647 ∧ 984465438<2147483647))
  omega
theorem addition : decode JFw_TX2_Head1.value+decode JFw_TX2_Tail1.value=decode value := by
  change (⟨⟨⟨67618853,2131009323⟩,⟨1541626496,237461256⟩⟩,⟨⟨701575401,413997160⟩,⟨1284607464,237657178⟩⟩⟩ : AspisWideTower.WideExact)+⟨⟨⟨1527237119,75368412⟩,⟨1184654964,389279168⟩⟩,⟨⟨872461572,1390225245⟩,⟨1801560076,746808260⟩⟩⟩=⟨⟨⟨1594855972,58894088⟩,⟨578797813,626740424⟩⟩,⟨⟨1574036973,1804222405⟩,⟨938683893,984465438⟩⟩⟩
  ext <;> norm_num [AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide

theorem source : FIp_NativeDots.fast_dots.four_dots_one
    (JFr_TX2_Windows.array (JFn_Values.position 0)) JFr_TX2_FirstLane.native 1#usize=ok value := by
  obtain ⟨out,run,co⟩ := JFs_TX2_Slot.source 0 1
  have us : Usize.ofNat (1:Fin 4).val (by have:=(1:Fin 4).isLt;scalar_tac)=1#usize := by
    apply UScalar.eq_of_val_eq;rfl
  rw [us] at run
  have add : FIo_Native.aspis_core.field.wide_exact.WideExact.add
      JFw_TX2_Head1.value JFw_TX2_Tail1.value=ok out := by
    simpa only [JFv_TX2_SlotMeaning.factor,JFw_TX2_Head1.source,
      JFw_TX2_Tail1.source,bind_tc_ok] using run
  have ch : FIo_WideValues.Canon JFw_TX2_Head1.value := by
    change ((67618853<2147483647 ∧ 2131009323<2147483647) ∧ (1541626496<2147483647 ∧ 237461256<2147483647)) ∧
      ((701575401<2147483647 ∧ 413997160<2147483647) ∧ (1284607464<2147483647 ∧ 237657178<2147483647))
    omega
  have ct : FIo_WideValues.Canon JFw_TX2_Tail1.value := by
    change ((1527237119<2147483647 ∧ 75368412<2147483647) ∧ (1184654964<2147483647 ∧ 389279168<2147483647)) ∧
      ((872461572<2147483647 ∧ 1390225245<2147483647) ∧ (1801560076<2147483647 ∧ 746808260<2147483647))
    omega
  have sem := (FIo_WideValues.add _ _ _ ch ct add).2
  have same : out=value := JFw_TX2_ValueUnique.native out value co canonical (sem.trans addition)
  exact same ▸ run
#print axioms canonical
#print axioms addition
#print axioms source
end AspisR1.JFw_TX2_Dot1
end
