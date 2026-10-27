import RPu_FIy_FrontierLoop
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_Frontier20
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Snapshot Selectors)

theorem value (a : Array NQ 16#usize) (s : Selectors) (d out : Array NQ 8#usize)
    (src returned : Snapshot) (ha : canonical a) (hh : canonical s.high) (hl : canonical s.low) (hd : canonical d)
    (hf : ∀ row∈src.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (success : pool_v1.pair_forest_semantic_terminal.public_digest_lanes_loop
      ⟨0#usize,20#usize⟩ a s d src=ok (out,returned)) :
    returned=src ∧ canonical out ∧ decoded out=FIy_FrontierLoop.model src s a 20 0 (decoded d) := by
  exact FIy_FrontierLoop.value 20 ⟨0#usize,20#usize⟩ a s d out src returned rfl (by rfl) ha hh hl hd hf success
#print axioms value
end AspisR1.FIy_Frontier20
end
