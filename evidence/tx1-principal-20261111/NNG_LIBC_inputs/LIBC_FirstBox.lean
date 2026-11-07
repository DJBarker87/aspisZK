import NMT_R2_ReachFull
set_option autoImplicit false
noncomputable section
namespace LIBC_FirstBox
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Snapshot := NMT_R2_Reach.Snapshot
abbrev LateError := NMT_R2_Reach.LateError
/-- Source fission immediately before pair_tree_profile.rs:665 Box::new.
Both unboxed decoder error and success are retained; only the reached Box
continuation is cut. No native invocation is used to define this probe. -/
def beforeBox (bytes : Slice U8) : Result (core.result.Result Snapshot LateError) := do
 let r ← pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes
 match r with
 | .Ok _ => .div
 | .Err e => do
   let err ← pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1.SnapshotConstructor e
   ok (.Err err)
theorem first_site (bytes : Slice U8) : beforeBox bytes = NMT_R2_Reach.markSnapshot bytes := by
 obtain ⟨r,hr⟩ := AspisS6NativeSnapshotDecodeTotal.decode_total bytes
 have source := congrArg (fun x => x.1) (NGF_NEX_SnapshotBoxOracle.result_state_effects bytes ())
 dsimp only at source
 unfold beforeBox NMT_R2_Reach.markSnapshot NMT_R2_Reach.snapshot
 rw [← source]
 unfold NGF_NEX_SnapshotBoxOracle.run
 rw [hr]
 cases r <;> rfl
/-- Entire parent substitution at the actual first allocation site, including
all paths that reject before that site. Later errors are never a premise. -/
theorem parent_cut (bytes : Slice U8) :
 NMT_R2_Reach.full beforeBox bytes = NMT_R2_Reach.full NMT_R2_Reach.markSnapshot bytes := by
 rw [show beforeBox=NMT_R2_Reach.markSnapshot from funext first_site]
theorem reached (bytes : Slice U8) : NMT_R2_Reach.reaches bytes=true ↔
 NMT_R2_Reach.full beforeBox bytes=.div := by
 rw [parent_cut]
 exact NMT_R2_Reach.reaches_iff bytes
theorem no_success (bytes : Slice U8) (v : Snapshot) : beforeBox bytes ≠ ok (.Ok v) := by
 rw [first_site]
 obtain ⟨r,hr⟩ := NMT_R2_Reach.snapshot_total bytes
 unfold NMT_R2_Reach.markSnapshot
 rw [hr]
 cases r <;> simp
/-- Arbitrary continuations on success are unreachable after the probe. -/
theorem continuation {A : Type} (bytes : Slice U8)
 (f g : core.result.Result Snapshot LateError → Result A)
 (errors : ∀ e,f (.Err e)=g (.Err e)) :
 (beforeBox bytes >>= f) = (beforeBox bytes >>= g) := by
 rw [first_site]
 obtain ⟨r,hr⟩ := NMT_R2_Reach.snapshot_total bytes
 unfold NMT_R2_Reach.markSnapshot
 rw [hr]
 cases r with
 | Ok v => rfl
 | Err e => exact errors e
#print axioms first_site
#print axioms parent_cut
#print axioms reached
#print axioms no_success
#print axioms continuation
end LIBC_FirstBox
