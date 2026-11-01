import NEG_RowBridge
set_option autoImplicit false
noncomputable section
namespace NEG_RowCertificate
open Aeneas Aeneas.Std Result
abbrev Power := NEG_RowAssociation.Power
/-- Both equalities concern the same result and the same original full carrier.
This is a model certificate; native/iterator/P6 transport remains external. -/
theorem same_run (row : Array U64 4#usize) (p : Power) (basis : U32) (terms : Nat)
    (canonical : ∀ j : Usize, j.val<4 →
      (S7Kani2OwnedRow.limb (NEG_RowBridge.modelPower p) j).val<2147483647)
    (basisCanonical : basis.val<2147483647)
    (phase : ∀ j raw, j.val<4 → Array.index_usize row j=ok raw →
      raw.val<2^34+(terms%4)*(2^31-2)^2) :
    ∃ out,
      NEG_RowIsolated.update_residue_row row p basis (decide (terms%4=3))=ok out ∧
      S7Kani2OwnedRow.residue_owned row (NEG_RowBridge.modelPower p) basis
        (decide (terms%4=3))=ok out := by
  obtain ⟨out,run⟩ := NEG_RowBridge.from_phase row p basis terms canonical basisCanonical phase
  refine ⟨out,run,?_⟩
  rw [NEG_RowAssociation.emitted_to_owned] at run
  exact run

/-- Source-emitted equality transports arbitrary caller continuations, including
rejections and divergence, without an independent successful execution. -/
theorem continuation {α : Type} (row : Array U64 4#usize) (p : Power)
    (basis : U32) (flush : Bool) (k : Array U64 4#usize → Result α) :
    (do let out ← NEG_RowIsolated.update_residue_row row p basis flush; k out) =
    (do let out ← S7Kani2OwnedRow.residue_owned row (NEG_RowBridge.modelPower p) basis flush; k out) := by
  rw [NEG_RowAssociation.emitted_to_owned]
#print axioms same_run
#print axioms continuation
end NEG_RowCertificate
end
