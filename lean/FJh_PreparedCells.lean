import FJh_MapCells
import FJa_PreparedMap
import FJe_Sum3Value
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_PreparedCells
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_PreparedNew (NP prepared)
open FJe_Sum3Value (cell)
/-- Prepared-map association for every selected output, on its original weights. -/
theorem value (w : Array NQ 3#usize) (p : Array NP 3#usize)
    (cw : FIw_ArrayValue.canonical w)
    (run : FIq_Native.core.array.Array.map (BuiltinFnMut NQ NP) w
      field.PreparedQm31Multiplier.new=ok p) (i : Fin 3) :
    ExtractedMaskPreparedState.PreparedFor (prepared (cell p i)) (qm (cell w i)) := by
  have rel := FJa_PreparedMap.value w p cw run
  exact FJh_MapCells.get rel i.val (by rw [w.property];exact i.isLt)
    (by rw [p.property];exact i.isLt)
#print axioms value
end AspisR1.FJh_PreparedCells
end
