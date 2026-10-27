import LPa_BoundaryPure
import LPa_AddInvariant
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal
set_option autoImplicit false
namespace LPa.Boundary

theorem field_zero : LPa.Add.field qzero qzero = qzero := by rfl

theorem fold_zero (n : Nat) :
    (List.replicate n qzero).foldl LPa.Add.field qzero = qzero := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.foldl_cons, field_zero, ih]

def zeroPolynomial : Array aspis_core.field.QM31 28#usize :=
  ⟨List.replicate 28 qzero,by simp⟩

theorem zero_accepted : r1_semantic.semantic_boundary zeroPolynomial = ok qzero := by
  rw [← loop_eq_model, loop_pure]
  have head : Array.index_usize zeroPolynomial 0#usize = ok qzero := by rfl
  simp only [head, bind_tc_ok]
  change ok ((List.replicate 28 qzero).foldl LPa.Add.field qzero) = ok qzero
  rw [fold_zero]

#print axioms field_zero
#print axioms fold_zero
#print axioms zero_accepted
end LPa.Boundary
