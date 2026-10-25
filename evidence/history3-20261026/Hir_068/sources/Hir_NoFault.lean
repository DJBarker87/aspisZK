import Hir_AcceptedDriver
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_NoFault
open Aeneas Aeneas.Std Result SdkC_Source

/-- Only syscall status is constrained. Source-level errors, parser rejection,
copy/cleanup failure and divergence in pure steps remain allowed. The universal
continuation quantifier is essential for an ALL-WORLD probability transport. -/
def NoFault (hashv : Parts → Result Digest) {A : Type} : Code A → Prop
  | .done _ => True
  | .step result k => match result with
    | .ok value => NoFault hashv (k value)
    | .fail _ | .div => True
  | .read parts k => (∃ digest, hashv parts = .ok digest) ∧ ∀ digest, NoFault hashv (k digest)

theorem of_total (hashv : Parts → Result Digest)
    (total : ∀ parts, ∃ digest, hashv parts = .ok digest) {A : Type} (code : Code A) :
    NoFault hashv code := by
  induction code with
  | done _ => trivial
  | step result k ih => cases result with
    | ok value => exact ih value
    | fail _ => trivial
    | div => trivial
  | read parts k ih => exact ⟨total parts,ih⟩

#print axioms of_total
end AspisR1.Hir_NoFault
end
