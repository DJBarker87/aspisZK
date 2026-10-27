import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_EmissionReached
open Aeneas Aeneas.Std Result

theorem source (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts data slot=ok (.Ok ())) :
    ∃ statement,(ops.op53 statement)=ok (.Ok ()) := by
  unfold AdapterRw.r1_pool_adapter.owned.stage2_owned at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,accepted⟩
#print axioms source
end AspisR1.JGx_EmissionReached
end
