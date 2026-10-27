import R1Z.PV_RE_BindTransportB10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_LayoutPrefix1002B
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev Expander := aspis_prover.state_only_hiding.SeedExpander
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
theorem entered {S : Type} (inst : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (hash : Hash) (binding : Array U8 32#usize) (context : Context)
    (entropy : Array U8 32#usize) (store : S)
    (cells : Slice aspis_statement.trace_v4.TraceCell) (active : Array Bool 1024#usize)
    (store1 : S) (h0 : inst.reserve store context.statement_digest context.mask_nonce = .ok (true,store1))
    (seed : Array U8 32#usize) (h1 : aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy = .ok (.Ok seed)) :
    ∃ next, aspis_prover.state_only_hiding.build_mask_material_for_layout inst hash binding context entropy store cells active =
      (aspis_prover.state_only_hiding.SeedExpander.new hash seed >>= next) := by
  unfold aspis_prover.state_only_hiding.build_mask_material_for_layout
  change ∃ next, (inst.reserve store context.statement_digest context.mask_nonce >>= _) = _
  rw [h0]
  change ∃ next, (aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy >>= _) = _
  rw [h1]
  simp only [bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_LayoutPrefix1002B
