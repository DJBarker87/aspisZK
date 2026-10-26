import PoolN_Verifier
import PoolM_NativeCancelReject
set_option autoImplicit false
namespace AspisR1.PoolL_VerifierScopes
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
/-- Preserve every physical observation of the accepted V2 wrapper heap.
This retains the inherited native/allocator/runtime interpretation boundaries;
it does not assert a new source-to-ELF admission instance. -/
theorem V2_observation {A V : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (after : Heap (Nat → Record)) (read : Heap (Nat → Record) → V)
    (accepted : second native allocator e program data slot state = ok (.Ok (after,final))) :
    read after = read e.heap := congrArg read (PoolN_Verifier.V2_frame _ _ _ _ _ _ _ _ _ accepted)
/-- V1 exact occupied source gate, including arbitrary successful earlier
parser Result; errors before the gate also cannot accept. -/
theorem V1_prefix (bytes : Slice U8) (head : U8)
    (nonempty : 0 < bytes.val.length) (read : Slice.index_usize bytes 0#usize = ok head)
    (nonzero : head ≠ 0#u8)
    (before : Result (core.result.Result Unit AdapterRw.solana_program_error.ProgramError)) :
    PoolM_NativeCancelGuard.thenResult before
      (AdapterRw.r1_pool_adapter.owned.require_zero bytes) ≠ ok (.Ok ()) := by
  rw [PoolN_Verifier.V1_occupied_gate bytes head nonempty read nonzero]
  intro yes
  have h := (PoolM_NativeCancelReject.then_accepted _ _).mp yes
  cases h.2
#print axioms V2_observation
#print axioms V1_prefix
end AspisR1.PoolL_VerifierScopes
