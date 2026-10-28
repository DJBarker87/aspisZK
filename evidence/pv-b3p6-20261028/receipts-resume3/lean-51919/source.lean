import PV_B3P_FreeTotal132
import PV_B3P_MaskModel132
import PV_B3P_Offset226V3
namespace PV_B3P_MaskFreeLaw132
open Aeneas Aeneas.Std PV_B3P_132
set_option autoImplicit false

theorem free_eq (r c : Usize) :
    reference132.free r c = .ok (decide (PV_B3P_MaskModel132.free r.val c.val)) := by
  obtain ⟨rem,hrem,hval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=r) (y:=16#usize) (by decide))
  have hv : rem.val = r.val % 16 := by simpa using hval
  unfold reference132.free
  simp only [hrem,lift,bind_tc_ok,PV_B3P_FreeTotal132.if_ok]
  by_cases hr : r.val < 912
  · have h : r < 912#usize := by scalar_tac
    simp only [h,↓reduceIte,PV_B3P_MaskModel132.free,hr]
    apply congrArg Result.ok
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    scalar_tac
  · have h : ¬ r < 912#usize := by scalar_tac
    simp only [h,↓reduceIte,PV_B3P_MaskModel132.free,hr]
    by_cases hr' : r.val < 1008
    · have h' : r < 1008#usize := by scalar_tac
      simp only [h',hr',↓reduceIte]
      apply congrArg Result.ok
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.not_eq_true, ite_eq_iff]
      simp [PV_B3P_MaskModel132.free,hr,hr',PV_B3P_MaskShape132.localUsed] at *
      scalar_tac <;> split <;> scalar_tac
    · have h' : ¬ r < 1008#usize := by scalar_tac
      have hsub := PV_B3P_Offset226V3.sub_value r 1008#usize (by scalar_tac)
      simp only [h',hr',↓reduceIte]
      apply congrArg Result.ok
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, Bool.not_eq_true, ite_eq_iff]
      simp [PV_B3P_MaskModel132.free,hr,hr',PV_B3P_MaskModel132.valueUsed] at *
      scalar_tac <;> split <;> scalar_tac
#print axioms free_eq
end PV_B3P_MaskFreeLaw132
