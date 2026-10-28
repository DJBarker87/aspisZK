import R1Z.PV_RunJoin_ByteEquality29
import R1Z.PV_RunJoin_DecodedFrontier29
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SnapshotDomain29
open Aeneas Aeneas.Std Result R0Z.WriterRefine AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def zero : Array U8 32#usize := Array.repeat 32#usize 0#u8

def Domain (s : PoolV1PairLiveSnapshotV1) : Prop :=
  s.pool ≠ zero ∧ s.deployment_domain ≠ zero ∧ s.sequence=s.next_pair_index ∧
  s.next_pair_index.val < 1048576 ∧ Canon8 s.current_root ∧
  ∀ l : Fin 20, Canon8 s.frontier.val[l.val]!

def result (s : PoolV1PairLiveSnapshotV1) : core.result.Result Unit PoolV1PairLiveSnapshotErrorV1 :=
  if s.pool=zero ∨ s.deployment_domain=zero then .Err .ZeroRequiredBinding
  else if s.sequence≠s.next_pair_index then .Err .SequenceIndexMismatch
  else if 1048576 ≤ s.next_pair_index.val then .Err .TreeFull
  else if Canon8 s.current_root ∧ (∀ l : Fin 20, Canon8 s.frontier.val[l.val]!) then .Ok ()
  else .Err .NonCanonicalDigest

theorem capacity : POOL_V1_PAIR_CAPACITY = ok 1048576#u64 := by rfl
#print axioms capacity

theorem frontier_result (a : PV_RunJoin_DecoderFrontier29.Frontier) :
    validate_pool_v1_pair_live_snapshot_v1_loop a 0#usize =
      ok (if (∀ l : Fin 20, Canon8 a.val[l.val]!) then .Ok () else .Err .NonCanonicalDigest) := by
  rw [PV_RunJoin_DecoderFrontier29.frontier_loop a 0#usize (by decide)]
  have he : PV_RunJoin_DecoderFrontier29.Tail a (0#usize).val ↔
      (∀ l : Fin 20, Canon8 a.val[l.val]!) := by
    constructor
    · intro h l; exact h l.val (by change 0 ≤ l.val;omega) l.isLt
    · intro h l _ hl; exact h ⟨l,hl⟩
  rw [propext he]
#print axioms frontier_result

/-- Exact success and first-error guard normal form of the actual extracted
snapshot validator, including active-frontier canonicality. -/
theorem source_result (s : PoolV1PairLiveSnapshotV1) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (result s) := by
  unfold validate_pool_v1_pair_live_snapshot_v1
  simp only [PV_RunJoin_ByteEquality29.array_result,bind_tc_ok]
  rw [capacity,PV_RunJoin_DecoderFrontier29.digest_result]
  simp only [bind_tc_ok,frontier_result]
  unfold result zero
  simp only [decide_eq_true_eq,UScalar.le_equiv,UScalar.ofNatCore_val_eq]
  split_ifs <;> simp_all
#print axioms source_result

theorem success_iff (s : PoolV1PairLiveSnapshotV1) :
    validate_pool_v1_pair_live_snapshot_v1 s = ok (.Ok ()) ↔ Domain s := by
  rw [source_result]
  unfold result Domain
  split_ifs <;> simp_all
#print axioms success_iff
end R1Z.PV_RunJoin_SnapshotDomain29
