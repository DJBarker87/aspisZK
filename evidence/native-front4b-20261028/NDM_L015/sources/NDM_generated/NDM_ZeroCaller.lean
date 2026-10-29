import S2W_D189Entry
import NDM_ZeroCut
set_option autoImplicit false
namespace NDM_ZeroCaller
open Aeneas Aeneas.Std Result
open AspisR1.S2W_D189Entry
open AdapterRw

/-- Every successful checkpoint-data read of the computed entry snapshot establishes
 the native one-iteration bound. No accepted output or length consistency premise is added. -/
theorem checkpoint_domain (e : Entry) (ops : Ops) (bytes : Slice U8)
 (read : r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot 2 1768 1768)=ok (.Ok bytes)) :
 bytes=e.buffers (e.handles 2).1 ∧ bytes.val.length=1768 := by
 obtain ⟨v,stored,view⟩ := AspisR1.S2W.SnapshotJoin.data_success ops (e.snapshot 2 1768 1768) bytes read
 change (if (e.buffers (e.handles 2).1).val.length=1768 ∨
  (e.buffers (e.handles 2).1).val.length=1768 then core.result.Result.Ok (e.buffers (e.handles 2).1)
  else core.result.Result.Err solana_program_error.ProgramError.InvalidAccountData)=core.result.Result.Ok v at stored
 split at stored
 · rename_i admitted
   have equal := core.result.Result.Ok.inj stored
   subst v
   have same : bytes=e.buffers (e.handles 2).1 := by simpa only [alloc.vec.Vec.deref] using view.symm
   exact ⟨same,by rw [same];exact admitted.elim id id⟩
 · cases stored

/-- The existing model induction is instantiated on precisely the reached caller buffer. -/
theorem caller (e : Entry) (ops : Ops) (bytes : Slice U8)
 (read : r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot 2 1768 1768)=ok (.Ok bytes)) :
 r1_pool_adapter.owned.require_zero bytes = ok
  (if NDG_ZeroRun.AllZero bytes 0 then .Ok () else .Err .AccountAlreadyInitialized) := by
 have size := (checkpoint_domain e ops bytes read).2
 exact NDG_ZeroRun.value bytes (by omega)

#print axioms checkpoint_domain
#print axioms caller
end NDM_ZeroCaller
