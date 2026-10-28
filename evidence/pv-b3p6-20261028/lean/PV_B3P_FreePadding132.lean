import PV_B3P_FreeTotal132
import PV_B3P_MaskModel132
namespace PV_B3P_FreePadding132
open Aeneas Aeneas.Std PV_B3P_132
set_option autoImplicit false

theorem value (row column : Usize) (hr : row.val < 912) :
    reference132.free row column = .ok (decide (PV_B3P_MaskModel132.free row.val column.val)) := by
  have hb : row < 912#usize := by scalar_tac
  obtain ⟨r,he,hval⟩ := WP.spec_imp_exists
    (UScalar.rem_spec (x:=row) (y:=16#usize) (by decide))
  have hv : r.val = row.val%16 := by simpa using hval
  have htest : (r ≥ 13#usize) ↔ 13 ≤ row.val%16 := by
    change 13 ≤ r.val ↔ 13 ≤ row.val%16
    rw [hv]
  rw [reference132.free,if_pos hb,he]
  simp only [bind_tc_ok,PV_B3P_MaskModel132.free,hr,↓reduceIte,htest]
#print axioms value
end PV_B3P_FreePadding132
