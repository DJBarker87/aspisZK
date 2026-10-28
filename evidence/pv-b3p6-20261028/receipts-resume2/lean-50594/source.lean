import PV_B3P_Emission132
import PV_B3P_MaskCasts132
namespace PV_B3P_MaskStep132
open Aeneas Aeneas.Std PV_B3P_132
set_option autoImplicit false

theorem write_retained (out : Array reference132.Cell 3803#usize)
    (count row column : Usize) (hr : row.val < 1024) (hc : count.val < 3803)
    (hf : reference132.free row column = .ok true) :
    ∃ out', reference132.cells_loop0_loop0.body column out count row =
      .ok (.cont (out',Usize.wrapping_add count 1#usize,Usize.wrapping_add row 1#usize)) ∧
      out' = out.set count ⟨UScalar.cast .U16 row,UScalar.cast .U8 column⟩ := by
  have hb : row < 1024#usize := by scalar_tac
  have hindex : count.val < out.val.length := by rw [out.property]; simpa using hc
  obtain ⟨out',hout',hval⟩ := WP.spec_imp_exists
    (Array.update_spec out count (⟨UScalar.cast .U16 row,UScalar.cast .U8 column⟩ : reference132.Cell) hindex)
  refine ⟨out',?_,hval⟩
  simp only [reference132.cells_loop0_loop0.body,hb,↓reduceIte,hf,lift,bind_tc_ok,hout']

theorem skip (out : Array reference132.Cell 3803#usize)
    (count row column : Usize) (hr : row.val < 1024)
    (hf : reference132.free row column = .ok false) :
    reference132.cells_loop0_loop0.body column out count row =
      .ok (.cont (out,count,Usize.wrapping_add row 1#usize)) := by
  have hb : row < 1024#usize := by scalar_tac
  simp only [reference132.cells_loop0_loop0.body,hb,↓reduceIte,hf,lift,bind_tc_ok,Bool.false_eq_true]

theorem inner_done (out : Array reference132.Cell 3803#usize)
    (count row column : Usize) (hr : 1024 ≤ row.val) :
    reference132.cells_loop0_loop0.body column out count row = .ok (.done (out,count)) := by
  have hb : ¬ row < 1024#usize := by scalar_tac
  simp only [reference132.cells_loop0_loop0.body,hb,↓reduceIte]

theorem outer_done (out : Array reference132.Cell 3803#usize)
    (count column : Usize) (hc : 16 ≤ column.val) :
    reference132.cells_loop0.body out count column = .ok (.done (out,count)) := by
  have hb : ¬ column < 16#usize := by scalar_tac
  simp only [reference132.cells_loop0.body,hb,↓reduceIte]

#print axioms write_retained
#print axioms skip
#print axioms inner_done
#print axioms outer_done
end PV_B3P_MaskStep132
