import NEA_Reference.Funs
import NDH_Geometry
set_option autoImplicit false
namespace NEA_Index
open Aeneas Aeneas.Std Result

def PacketDomain (_ : Usize) : Prop := True

theorem all_inputs (x : Usize) :
    NEA_Reference.fibre_new_ref x = ok
      (if x < 262144#usize then core.result.Result.Ok x else core.result.Result.Err 1#u8) := by
  simp only [NEA_Reference.fibre_new_ref]
  split <;> rfl

theorem accepted (x y : Usize)
    (run : NEA_Reference.fibre_new_ref x = ok (core.result.Result.Ok y)) :
    y = x ∧ x.val < 262144 := by
  rw [all_inputs] at run
  split at run
  · cases run
    exact ⟨rfl, by scalar_tac⟩
  · cases run

/-- The constructor's accepted value is the exact index consumed by the actual
emitted geometry call, whose FibreIndex carrier is Usize. No helper stand-in. -/
theorem fibre_caller (ops : AspisR1QueryGeometryActual.CM31Ops) (x y : Usize)
    (run : NEA_Reference.fibre_new_ref x = ok (core.result.Result.Ok y)) :
    AspisR1QueryGeometryActual.fast_domain.fibre_point ops y =
      AspisR1QueryGeometryActual.fast_domain.fibre_point ops x := by
  rw [(accepted x y run).1]

theorem aligned_domain (u : Nat) (bound : u < 262144) :
    u / 4 * 4 < 262144 ∧ u / 4 * 4 + 3 < 262144 := by omega

theorem canonical_index (x : Usize) (bound : x.val < 262144) :
    NEA_Reference.fibre_new_ref x = ok (core.result.Result.Ok x) := by
  rw [all_inputs]
  have h : x < 262144#usize := by scalar_tac
  rw [if_pos h]

#print axioms all_inputs
#print axioms accepted
#print axioms fibre_caller
#print axioms aligned_domain
#print axioms canonical_index
end NEA_Index
