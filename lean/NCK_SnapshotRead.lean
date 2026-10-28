import NCK_Getters
import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_SnapshotRead
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers
/-- The two top-body account reads select these original snapshots. -/
theorem proof_index (e : Entry) :
    Slice.index_usize (e.second secondSizes) 0#usize =
      ok (e.snapshot 0 58295 58295) := rfl
 theorem checkpoint_index (e : Entry) :
    Slice.index_usize (e.second secondSizes) 6#usize =
      ok (e.snapshot 6 1768 1768) := rfl
/-- Successful snapshot read determines original bytes and admitted bounds,
including the deferred-error branch. No allocation or hash identity premise. -/
theorem original_bytes (ops : _root_.AdapterRw.Ops) (e : Entry) (a l₁ l₂ : Nat)
    (out : Slice U8)
    (read : _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
      (e.snapshot a l₁ l₂) = ok (.Ok out)) :
    out.val = (e.buffers (e.handles a).1).val ∧
    ((e.buffers (e.handles a).1).val.length = l₁ ∨
     (e.buffers (e.handles a).1).val.length = l₂) := by
  by_cases admitted : (e.buffers (e.handles a).1).val.length = l₁ ∨
      (e.buffers (e.handles a).1).val.length = l₂
  · simp only [Entry.snapshot, if_pos admitted,
      _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data] at read
    have same := core.result.Result.Ok.inj (Result.ok.inj read)
    exact ⟨by rw [←same]; rfl,admitted⟩
  · have never := AdapterRw.Cuts.error_bind_ne_ok
      (ops.op35 _root_.AdapterRw.solana_program_error.ProgramError.InvalidAccountData) out
    exfalso
    apply never
    simpa only [Entry.snapshot, if_neg admitted,
      _root_.AdapterRw.r1_pool_adapter.owned.OwnedAccount.data] using read
#print axioms proof_index
#print axioms checkpoint_index
#print axioms original_bytes
end AspisR1.NCK_SnapshotRead
end
