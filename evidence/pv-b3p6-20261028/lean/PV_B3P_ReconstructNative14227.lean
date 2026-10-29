import PV_B3P_TransitionLoan14227
import PV_B3P_ReconstructBinding9227
import PV_B3P_ReconstructLink13227
namespace PV_B3P_Loans14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
abbrev ReconstructInput14 := Array aspis_core.field.QM31 16#usize
/-- Source interpreter for the immutable borrowed argument. Receiver addition,
indexed argument read, second addition, and the pre-decrement loop order are
those of the frozen deployed host body. The caller loan is never changed. -/
def reconstruct_native14 (view : Shared14 ReconstructInput14) : Result aspis_core.field.QM31 := do
  let acc ← Array.index_usize view.value 9#usize
  loop (reverse_body (reconstruct_step view.value)) (acc,9#usize)

theorem reconstruct_native_binding14 (view : Shared14 ReconstructInput14) :
    reconstruct_native14 view = reference_terminal.reconstruct_10 view.value :=
  reconstruct_body_binding view.value

theorem reconstruct_source_read_bound14 (index : Usize) (loop_bound : index.val ≤ 9)
    (nonzero : 0 < index.val) :
    (Usize.wrapping_sub index 1#usize).val < 16 := by
  rw [PV_B3P_Offset226V3.sub_value index 1#usize (by scalar_tac)]
  change index.val-1 < 16
  omega

theorem reconstruct_fixed_read_bound14 : (9#usize).val < (16#usize).val := by decide

/-- Any complete-Result caller continuation transports, including Err/fail/div
in downstream operations; this law does not assume field canonicality. -/
theorem reconstruct_native_continuation14 {β : Type} (view : Shared14 ReconstructInput14)
    (next : aspis_core.field.QM31 → Result β) :
    (do let result ← reconstruct_native14 view; next result) =
      (do let result ← reference_terminal.reconstruct_10 view.value; next result) := by
  rw [reconstruct_native_binding14]
#print axioms reconstruct_native_binding14
#print axioms reconstruct_source_read_bound14
#print axioms reconstruct_fixed_read_bound14
#print axioms reconstruct_native_continuation14
end PV_B3P_Loans14227
