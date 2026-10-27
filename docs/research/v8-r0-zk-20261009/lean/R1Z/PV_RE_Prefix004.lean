import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix004
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.sync_directory` (op14).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (directory : std.path.Path) :
  ∃ next, @aspis_prover.state_only_entropy.sync_directory _ _ directory =
    (std.fs.File.open (Shared0T.Insts.CoreConvertAsRef
      std.path.Path.Insts.CoreConvertAsRefPath) directory >>= next) := by
  unfold aspis_prover.state_only_entropy.sync_directory
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix004
