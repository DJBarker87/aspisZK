import JGx_EmissionReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_EmissionObstruction
open Aeneas Aeneas.Std Result

/-- Rejecting emit_result leaves refute only uniform success over arbitrary
source dictionaries, not the retained real fixture or any release premise. -/
theorem source (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (reject : ∀ statement,ops.op53 statement=ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)) :
    AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot≠ok (.Ok ()) := by
  intro accepted
  obtain ⟨statement,emitted⟩ := JGx_EmissionReached.source ops program accounts data slot accepted
  rw [reject statement] at emitted
  cases emitted
#print axioms source
end AspisR1.JGx_EmissionObstruction
end
