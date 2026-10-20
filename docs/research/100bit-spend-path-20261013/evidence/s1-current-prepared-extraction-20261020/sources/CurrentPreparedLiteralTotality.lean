import CurrentPreparedScratchModel
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PreparedScratchControl

private theorem checked_add_exact {ty : UScalarTy} (a b c : UScalar ty)
    (hc : c.val = a.val + b.val) : a + b = ok c := by
  obtain ⟨z, hz, _⟩ := WP.spec_imp_exists
    (UScalar.add_spec (x := a) (y := b) (by scalar_tac))
  have he : z = c := by scalar_tac
  simpa only [he] using hz

/-- All checked integer additions in the current Prepared::new body are
in range, independently of whether any child API succeeds. Allocation,
Option.unwrap and the child samplers/powers/claim are separate boundaries. -/
theorem checked_literal_additions_total :
    32#usize + 224#usize = ok 256#usize ∧
    30#u8 + 1#u8 = ok 31#u8 ∧
    31#u8 + 1#u8 = ok 32#u8 := by
  exact ⟨checked_add_exact _ _ _ (by scalar_tac),
    checked_add_exact _ _ _ (by scalar_tac),
    checked_add_exact _ _ _ (by scalar_tac)⟩

#print axioms checked_literal_additions_total
end AspisR1PublicPreparation.PreparedScratchControl
