import NDO_JGa_Reconstruct
import RPv_JFy_PreparedSteps
import RPv_FIy_ValueTail
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_ValueTail
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)

@[step] theorem source (o : state_only_poseidon.StateOnlyPoseidonOpenings)
    (range : Array field.QM31 33#usize) (hz : canonical o.z) (hs : canonical o.succ_z)
    (hx : canonical o.xor12_z) (hr : canonical range) :
    FIy_ValueTail.run o range ⦃ out => canonical out ⦄ := by
  unfold FIy_ValueTail.run
  step* <;> first | assumption | scalar_tac
#print axioms source
end AspisR1.JGa_ValueTail
end
