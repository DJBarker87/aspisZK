import BinRawByteCutRecovery
import BinRawByteCutStability
import BinMultiproof

/-! Binding of an opening authenticated by ONE merged multiproof (the Aspis
one-transaction format: one multiproof per tree over all 22 queries), in R1's
binary commitment model.

Kind of result: MODEL THEOREM in R1's Bin commitment model (random oracle `H`,
literal oracle log `tr`, the single five-target binary collision event
`AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q`). It composes
two R1 theorems, both index-set generic:
* `BinMultiproof.accepted_path` (every member of an accepted level-at-a-time
  multiproof has an accepted single path whose hash inputs are among the
  multiproof's hash inputs), and
* `BinRawByteCutRecovery.recover_at_first_commitment` (an accepted path whose
  reads are in the log recovers, from the log strictly before the root's
  commitment frame, exactly the opened leaf, unless the collision event).
No new event and no new constant: the exception is R1's event at R1's read
budget `Q`.

NOT established here (source obligations, open): that the Rust function
`multiproof::verify_counting_merged` with `merkle_verdict` refines
`BinMultiproof.Accept` at depth 18 on the distinct sorted index set; that
`merged_tree`'s duplicate rule gives `BinMultiproof.Dedup`; that its leaf hash
is `leafInput tag packed salt` with R1's tags and widths; and that every hash
input it issues is in the log `tr`. -/

set_option autoImplicit false
noncomputable section
namespace AspisPairResidual.Merkle

open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisR1 AspisR1.BinMerkle32Path AspisR1.BinMerkle32Leaf

/-- A member of an accepted merged multiproof is recovered from the log cut
at the commitment frame of its root (R1's three-commitment recovery form). -/
theorem merged_member_recovery (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    {depth : Nat} {active : BinMultiproof.Active} {v : BinMultiproof.Values}
    {nodes : List Digest} {trace : List (List BinMerkle32Path.Byte)} (root : State)
    (hacc : BinMultiproof.Accept H root depth active v nodes trace)
    (htrace : ∀ a ∈ trace, Read tr a)
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (i : Nat) (hi : i ∈ active) (hleaf : v i = H (leafInput tag packed salt))
    (hleafRead : Read tr (leafInput tag packed salt))
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    BinRawByteCutStability.recoverAt tag width (BinRawByteCutRecovery.cut tr frame)
      (BinMultiproof.slots depth i) root = some (packed, salt) := by
  obtain ⟨path, hroot, hsub⟩ := BinMultiproof.accepted_path hacc i hi
  rw [hleaf] at hroot hsub
  have hr := BinRawByteCutRecovery.recover_at_first_commitment iv H tr Q hcons hQ hout
    tag width packed salt hw hs path root frame j hframe hpred
    (by rw [BinMerkleProgram.eval_leafProgram]; exact hroot)
    (by
      intro a ha
      rw [BinMerkleProgram.eval_leafProgram] at ha
      change a ∈ ((fullTrace H path (leafInput tag packed salt)).map
        (fun b => (b, H b))).map Prod.fst at ha
      simp only [List.map_map, Function.comp_def, List.map_id'] at ha
      unfold fullTrace at ha
      rcases List.mem_cons.mp ha with he | hm
      · subst he; exact hleafRead
      · exact htrace a (hsub hm))
  exact hr

/-- Per-query form: an accepted merged multiproof over a deduplicated batch
of `(index, leaf digest)` pairs (equal indices with different leaves rejected)
binds every listed leaf. -/
theorem merged_query_recovery (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    {depth : Nat} {active : BinMultiproof.Active} {v : BinMultiproof.Values}
    {nodes : List Digest} {trace : List (List BinMerkle32Path.Byte)} (root : State)
    (hacc : BinMultiproof.Accept H root depth active v nodes trace)
    (htrace : ∀ a ∈ trace, Read tr a)
    (batch : List (Nat × Digest)) (hd : BinMultiproof.Dedup batch active v)
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (i : Nat) (hq : (i, H (leafInput tag packed salt)) ∈ batch)
    (hleafRead : Read tr (leafInput tag packed salt))
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    BinRawByteCutStability.recoverAt tag width (BinRawByteCutRecovery.cut tr frame)
      (BinMultiproof.slots depth i) root = some (packed, salt) := by
  obtain ⟨hi, hv⟩ := hd _ hq
  exact merged_member_recovery iv H tr Q hcons hQ hout root hacc htrace tag width
    packed salt hw hs i hi hv hleafRead frame j hframe hpred

/-- The attack in plain terms: two different openings `(packed, salt)` and
`(packed', salt')` of the same index under the same root, each authenticated
by an accepted merged multiproof whose reads are in the same log, cannot both
exist outside the collision event -- in particular one chosen after the
batching challenge cannot replace one fixed before it. -/
theorem no_second_opening (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    {depth : Nat} (root : State)
    {active active' : BinMultiproof.Active} {v v' : BinMultiproof.Values}
    {nodes nodes' : List Digest} {trace trace' : List (List BinMerkle32Path.Byte)}
    (hacc : BinMultiproof.Accept H root depth active v nodes trace)
    (hacc' : BinMultiproof.Accept H root depth active' v' nodes' trace')
    (htrace : ∀ a ∈ trace, Read tr a) (htrace' : ∀ a ∈ trace', Read tr a)
    (tag : BinMerkle32Path.Byte) (width : Nat) (packed salt packed' salt' : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    (hw' : packed'.length = width) (hs' : salt'.length = 32)
    (i : Nat) (hi : i ∈ active) (hi' : i ∈ active')
    (hleaf : v i = H (leafInput tag packed salt))
    (hleaf' : v' i = H (leafInput tag packed' salt'))
    (hleafRead : Read tr (leafInput tag packed salt))
    (hleafRead' : Read tr (leafInput tag packed' salt'))
    (frame : Bytes) (j : Fin 5) (hframe : Read tr frame)
    (hpred : BinRawByteCollisionTargets.pred j frame = some root) :
    packed = packed' ∧ salt = salt' := by
  have a := merged_member_recovery iv H tr Q hcons hQ hout root hacc htrace tag width
    packed salt hw hs i hi hleaf hleafRead frame j hframe hpred
  have b := merged_member_recovery iv H tr Q hcons hQ hout root hacc' htrace' tag width
    packed' salt' hw' hs' i hi' hleaf' hleafRead' frame j hframe hpred
  rw [a] at b
  exact Prod.ext_iff.mp (Option.some.inj b)

#print axioms merged_member_recovery
#print axioms merged_query_recovery
#print axioms no_second_opening

end AspisPairResidual.Merkle
end
