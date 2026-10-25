import S2W_D189Wrappers
import S2W_NativeConsolidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_SecondSnapshot
open Aeneas Aeneas.Std Result S2W_D189Entry
open S2W_NativeConsolidation

theorem second_index (e : Entry) :
    Slice.index_usize (e.second S2W_D189Wrappers.secondSizes) 6#usize =
      ok (e.snapshot 6 1768 1768) := rfl

/-- Any successful data accessor on the COMPUTED runtime snapshot reads the
original entry buffer; deferred length errors cannot manufacture a success. -/
theorem snapshot_bytes (ops : AdapterRw.Ops) (e : Entry) (a n m : Nat) (loaded : Slice U8)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops (e.snapshot a n m) = ok (.Ok loaded)) :
    loaded.val = (e.buffers (e.handles a).1).val := by
  obtain ⟨copied,stored,view⟩ := S2W.SnapshotJoin.data_success ops (e.snapshot a n m) loaded read
  change (if (e.buffers (e.handles a).1).val.length = n ∨ (e.buffers (e.handles a).1).val.length = m
    then core.result.Result.Ok (e.buffers (e.handles a).1)
    else core.result.Result.Err AdapterRw.solana_program_error.ProgramError.InvalidAccountData) =
      .Ok copied at stored
  split at stored
  · have same := core.result.Result.Ok.inj stored
    have left := congrArg (fun v => v.val) same
    have right := congrArg (fun v => v.val) view
    exact right.symm.trans left.symm
  · cases stored

theorem on_cuts (ops : AdapterRw.Ops) (e1 e2 : Entry) (saved : alloc.vec.Vec U8)
    (f : FirstCut) (s : SecondCut)
    (cuts : SourceCuts ops e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s) :
    s.checkpoint.val = (e2.buffers (e2.handles 6).1).val := by
  have same := Result.ok.inj (cuts.checkpoint2Index.symm.trans (second_index e2))
  have read := cuts.checkpoint2Read
  rw [same] at read
  exact snapshot_bytes ops e2 6 1768 1768 s.checkpoint read

#print axioms second_index
#print axioms snapshot_bytes
#print axioms on_cuts
end AspisR1.Hist_SecondSnapshot
end
