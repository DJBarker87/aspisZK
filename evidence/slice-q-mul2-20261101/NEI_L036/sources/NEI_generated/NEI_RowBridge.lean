import NEG_RowCertificate
import NEI_IteratorMeaning
set_option autoImplicit false
noncomputable section
namespace NEI_RowBridge
open Aeneas Aeneas.Std Result
abbrev Power := NEG_RowAssociation.Power
/-- Weak success domain: only the reached checked additions must fit. No
canonical field or phase restriction is introduced by the row bridge. -/
def Domain (row : Array U64 4#usize) (p : Power) (basis : U32) : Prop :=
 ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
  raw.val+(S7Kani2OwnedRow.limb (NEG_RowBridge.modelPower p) j).val*basis.val<2^64

theorem complete (row : Array U64 4#usize) (p : Power) (basis : U32)
 (flush : Bool) (domain : Domain row p basis) :
 ∃ out, NEG_RowIsolated.update_residue_row row p basis flush=ok out ∧
 S7Kani2OwnedRow.residue_owned row (NEG_RowBridge.modelPower p) basis flush=ok out := by
 obtain ⟨out, run⟩ := NEG_RowBridge.total row p basis flush domain
 exact ⟨out,run,by rw [← NEG_RowAssociation.emitted_to_owned];exact run⟩

/-- Exact all-outcome equality, for arbitrary continuation and raw input. -/
theorem continuation {α : Type} (row : Array U64 4#usize) (p : Power)
 (basis : U32) (flush : Bool) (k : Array U64 4#usize → Result α) :
 (do let out ← NEG_RowIsolated.update_residue_row row p basis flush; k out) =
 (do let out ← S7Kani2OwnedRow.residue_owned row (NEG_RowBridge.modelPower p) basis flush; k out) :=
 NEG_RowCertificate.continuation row p basis flush k
#print axioms complete
#print axioms continuation
end NEI_RowBridge
end
