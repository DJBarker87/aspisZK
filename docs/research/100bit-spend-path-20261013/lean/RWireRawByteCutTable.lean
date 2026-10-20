import BinRawByteCutStability
import R1TraceTableMembership
import RWireMerkleLogExt

/-! The commitment-cut recovered word depends only on the oracle table
available before the commitment's first read. Ordering and duplication of
consistent records do not matter. This supplies the table-only boundary
needed by a causal decoder; it does not construct that decoder or assert
its round-completion law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawByteCutTable

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open BinMerkle32Path BinMerkle32Leaf BinMerkleTable BinMerkleLeafRecovery BinMerkleRecordedLog
open BinRawByteCutRecovery BinRawByteCutStability

theorem replay_cut_eq_tableBefore (H : Bytes → State)
    (tr : List (Bytes × State)) (frame : Bytes)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    TraceTable.replay emptyTable (cut tr frame) = tableBefore emptyTable tr frame := by
  funext a
  have hc : ∀ q ∈ cut tr frame, q.2 = H q.1 := by
    intro q hq
    exact hcons q (List.mem_of_mem_take hq)
  rw [TraceTable.replay_empty_apply H (cut tr frame) hc a,
    tableBefore_eq H tr emptyTable frame a hcons]
  change (if Read (cut tr frame) a then some (H a) else none) =
    (if Before tr a frame then some (H a) else none)
  simp only [read_cut_iff]

theorem recover_eq_of_cut_table (iv : State) (H : Bytes → State)
    (tr represented : List (Bytes × State)) (Q : Nat) (frame : Bytes)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (htable : TraceTable.replay emptyTable represented = tableBefore emptyTable tr frame)
    (tag : BinMerkle32Path.Byte) (width : Nat) (slots : List (Fin 2)) (root : State) :
    recoverAt tag width (cut tr frame) slots root =
      recoverAt tag width represented slots root := by
  have hc : ∀ q ∈ cut tr frame, q.2 = H q.1 := by
    intro q hq
    exact hcons q (List.mem_of_mem_take hq)
  have heq : TraceTable.replay emptyTable (cut tr frame) =
      TraceTable.replay emptyTable represented :=
    (replay_cut_eq_tableBefore H tr frame hcons).trans htable.symm
  have hmem := TraceTableMembership.mem_eq_of_replay_eq H (cut tr frame) represented
    hc hrepresented heq
  have hsep : ∀ a b da db, (a, da) ∈ cut tr frame → (b, db) ∈ cut tr frame →
      H a = H b → a = b := by
    intro a b da db ha hb he
    have har : Read tr a := ((read_cut_iff tr frame a).mp
      (List.mem_map.mpr ⟨(a, da), ha, rfl⟩)).1
    have hbr : Read tr b := ((read_cut_iff tr frame b).mp
      (List.mem_map.mpr ⟨(b, db), hb, rfl⟩)).1
    by_contra hne
    exact AllAddressCollisionTrace.outputs_injective iv BinRawByteCollisionTargets.pred
      H tr Q hcons hQ hout a b har hbr hne he
  exact RWireMerkleLogExt.recover_eq H (cut tr frame) represented
    (cut_consistent H tr frame hcons) hsep hmem tag width slots root

/-- Any consistent representation of the current first-read table recovers
the same complete word as the eventual trace, outside one shared event. -/
theorem represented_word_eq_full (iv : State) (H : Bytes → State)
    (tr represented : List (Bytes × State)) (Q : Nat) (frame : Bytes)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (htable : TraceTable.replay emptyTable represented = tableBefore emptyTable tr frame)
    (tag : BinMerkle32Path.Byte) (width : Nat) (root : State)
    (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    (fun slots => recoverAt tag width represented slots root) =
      (fun slots => recoverAt tag width tr slots root) := by
  funext slots
  exact (recover_eq_of_cut_table iv H tr represented Q frame hcons hrepresented hQ hout
    htable tag width slots root).symm.trans
    (recover_stable iv H tr Q hcons hQ hout tag width slots root frame j hframe hpred)

#print axioms replay_cut_eq_tableBefore
#print axioms recover_eq_of_cut_table
#print axioms represented_word_eq_full

end AspisR1.RWireRawByteCutTable
end
