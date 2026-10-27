import R1Z.PV_RE_BindTransportB10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_LayoutPrefix1007
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
    (seed : Array U8 32#usize) (h1 : aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy = .ok (.Ok seed))
    (expander : Expander) (h2 : aspis_prover.state_only_hiding.SeedExpander.new hash seed = .ok expander)
    (inactive : Usize) (h3 : aspis_prover.state_only_hiding.first_inactive_row active = .ok inactive)
    (c1 : alloc.vec.Vec aspis_core.field.M31) (expander1 : Expander) (h4 : aspis_prover.state_only_hiding.sample_mask_cells expander (Slice.len cells) = .ok (.Ok c1,expander1))
    (columns : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize) (expander2 : Expander) (h5 : aspis_prover.state_only_hiding.sample_mask_columns expander1 inactive active = .ok (.Ok columns,expander2))
    (g : alloc.vec.Vec aspis_core.field.QM31) (expander3 : Expander) (h6 : aspis_prover.state_only_hiding.sample_mask_g expander2 inactive active = .ok (.Ok g,expander3)) :
    ∃ next, aspis_prover.state_only_hiding.build_mask_material_for_layout inst hash binding context entropy store cells active =
      (aspis_prover.state_only_hiding.sample_mask_h1_padding expander3 inactive active >>= next) := by
  unfold aspis_prover.state_only_hiding.build_mask_material_for_layout
  change ∃ next, (inst.reserve store context.statement_digest context.mask_nonce >>= _) = _
  rw [h0]
  change ∃ next, (aspis_prover.state_only_hiding.derive_state_only_mask_seed_from_entropy_ref hash binding context entropy >>= _) = _
  rw [h1]
  change ∃ next, (aspis_prover.state_only_hiding.SeedExpander.new hash seed >>= _) = _
  rw [h2]
  change ∃ next, (aspis_prover.state_only_hiding.first_inactive_row active >>= _) = _
  rw [h3]
  change ∃ next, (aspis_prover.state_only_hiding.sample_mask_cells expander (Slice.len cells) >>= _) = _
  rw [h4]
  change ∃ next, (aspis_prover.state_only_hiding.sample_mask_columns expander1 inactive active >>= _) = _
  rw [h5]
  change ∃ next, (aspis_prover.state_only_hiding.sample_mask_g expander2 inactive active >>= _) = _
  rw [h6]
  exact ⟨_,rfl⟩
#print axioms entered
end R1Z.PV_RE_LayoutPrefix1007
