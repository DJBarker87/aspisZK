import NDE_ClaimBridge
import NDE_RawBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDE_ClaimResult
open NDE_ClaimBridge

theorem columns :
    FIq_Native.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 = ok 28#usize := by
  simp only [FIq_Native.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1,
    FIq_Native.pool_v1.pair_forest_semantic_terminal.POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1,
    FIq_Native.state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS]
  have hmax := Usize.cMax_bound_concrete.1
  have h0 : (16#usize + 10#usize : Result Usize) = ok 26#usize := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=16#usize) (y:=10#usize) (by scalar_tac))
    have he : z = 26#usize := by scalar_tac
    simpa only [he] using hz
  have h1 : (26#usize + 2#usize : Result Usize) = ok 28#usize := by
    obtain ⟨z,hz,hv⟩ := WP.spec_imp_exists (UScalar.add_spec (x:=26#usize) (y:=2#usize) (by scalar_tac))
    have he : z = 28#usize := by scalar_tac
    simpa only [he] using hz
  simp only [h0,bind_tc_ok,h1]

theorem selected_claim (claims : Array Q 84#usize) (point column : Usize) :
    NDE_LiftBridge.mapResult fromRef (NDE_Reference4.claim_ref (claimsToRef claims) point column) =
    FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim claims point column := by
  simp only [NDE_Reference4.claim_ref, FIq_Native.pool_v1.pair_forest_semantic_terminal.selected_claim,
    columns,bind_tc_ok,NDE_RawBridge.map_bind,index_transport]

#print axioms columns
#print axioms selected_claim
end NDE_ClaimResult
