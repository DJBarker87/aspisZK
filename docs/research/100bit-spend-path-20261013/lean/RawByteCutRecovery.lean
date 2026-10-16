import RawByteCollisionTargets
import R1MerkleLogRecovery
import R1MerkleProgram

/-! Reuse the existing deterministic Merkle recovery theorem on the literal
oracle log strictly before a commitment's first read. The sole exceptional
event is the unrestricted-byte event already bounded by 12Q²/2^256.
Acceptance and containment of the actual opening-program reads remain
explicit source-refinement premises; no recovered whole word is assumed. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawByteCutRecovery

open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.UniformStateFirstHit
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog

/-- The literal chronological prefix, excluding the first commitment read. -/
def cut (tr : List (Bytes × State)) (frame : Bytes) : List (Bytes × State) :=
  tr.take (firstIdx frame tr)

theorem read_cut_iff (tr : List (Bytes × State)) (frame a : Bytes) :
    Read (cut tr frame) a ↔ Before tr a frame := by
  induction tr with
  | nil => simp [cut, Read, Before, firstIdx]
  | cons q rest ih =>
      rcases q with ⟨i, v⟩
      by_cases hf : i = frame
      · subst frame
        simp [cut, Read, Before, firstIdx]
      · by_cases ha : i = a
        · subst a
          simp [cut, Read, Before, firstIdx, hf]
        · simpa [cut, Read, Before, firstIdx, hf, ha, Ne.symm ha] using ih

theorem cut_consistent (H : Bytes → State) (tr : List (Bytes × State))
    (frame : Bytes) (hcons : ∀ q ∈ tr, q.2 = H q.1) :
    MerkleRecordedLog.Consistent H (cut tr frame) := by
  intro input output hin
  exact (hcons (input, output) (List.mem_of_mem_take hin)).symm

theorem target_cases (log : MerkleRecordedLog.Log) (root target : State)
    (h : target ∈ targets (nodes log) root) :
    target = root ∨ ∃ b, Read log b ∧ ∃ j : Fin 8,
      RawByteCollisionTargets.child j b = some target := by
  rcases List.mem_cons.mp h with heq | hchild
  · exact Or.inl heq
  · obtain ⟨⟨children, digest⟩, hentry, hslot⟩ := List.mem_flatMap.mp hchild
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hslot
    obtain ⟨input, hinput, hp⟩ := mem_nodes.mp hentry
    right
    refine ⟨input, List.mem_map.mpr ⟨(input, digest), hinput, rfl⟩, j, ?_⟩
    simp only [RawByteCollisionTargets.child, hp, Option.map_some]
    exact congrArg some hj

theorem opening_read_of_input (H : Bytes → State)
    {slots : List (Fin 8)} (path : Path slots) (leaf input : Bytes)
    (hin : input ∈ fullTrace H path leaf) :
    Read (eval H (MerkleProgram.leafProgram path leaf)).1 input := by
  rw [MerkleProgram.eval_leafProgram]
  change input ∈ ((fullTrace H path leaf).map (fun b => (b, H b))).map Prod.fst
  change input ∈ List.map Prod.fst
    (List.map (fun b => (b, H b)) (fullTrace H path leaf))
  exact List.mem_map.mpr ⟨(input, H input),
    List.mem_map.mpr ⟨input, hin, rfl⟩, rfl⟩

/-- An accepted opening is recovered from queries made strictly before the
first commitment-frame read, unless the single charged collision event occurs. -/
theorem recover_at_first_commitment (iv : State) (H : Bytes → State)
    (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv RawByteCollisionTargets.pred Q)
      emptyTable tr)
    (tag : Merkle32Path.Byte) (width : Nat) (packed salt : Bytes)
    (hw : packed.length = width) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (frame : Bytes) (j : Fin 11) (hframe : Read tr frame)
    (hpred : RawByteCollisionTargets.pred j frame = some root)
    (haccept : (eval H (MerkleProgram.leafProgram path
      (leafInput tag packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (MerkleProgram.leafProgram path
      (leafInput tag packed salt))).1 a → Read tr a) :
    recover (nodes (cut tr frame)) (leaves tag width (cut tr frame)) slots root =
      some (packed, salt) := by
  have hroot : root = foldPath H path (H (leafInput tag packed salt)) := by
    rw [MerkleProgram.eval_leafProgram] at haccept
    exact haccept.symm
  have hcases := MerkleLogRecovery.recover_or_bad H (cut tr frame)
    (cut_consistent H tr frame hcons) tag width packed salt hw hs path root hroot
  rcases hcases with hrecovered | hcollision | habsent
  · exact hrecovered
  · rcases hcollision with ⟨a, ha, b, hb, hne, heq⟩
    have hacut : Read (cut tr frame) a := ha
    have haread : Read tr a := ((read_cut_iff tr frame a).mp hacut).1
    have hbread : Read tr b := hopen b
      (opening_read_of_input H path (leafInput tag packed salt) b hb)
    exact False.elim (AllAddressCollisionTrace.outputs_injective iv
      RawByteCollisionTargets.pred H tr Q hcons hQ hout a b haread hbread hne heq)
  · rcases habsent with ⟨input, hin, hnot, htarget⟩
    have hread : Read tr input := hopen input
      (opening_read_of_input H path (leafInput tag packed salt) input hin)
    have hbefore : Before tr input frame := by
      rcases target_cases (cut tr frame) root (H input) htarget with
        hrootHit | ⟨b, hb, slot, hchild⟩
      · apply AllAddressCollisionTrace.parsed_target_after iv
          RawByteCollisionTargets.pred H tr Q hcons hQ hout j input frame hread hframe
        rw [hrootHit]
        exact hpred
      · have hbf := (read_cut_iff tr frame b).mp hb
        have hib : Before tr input b := by
          apply AllAddressCollisionTrace.parsed_target_after iv
            RawByteCollisionTargets.pred H tr Q hcons hQ hout
            ⟨slot.val, by omega⟩ input b hread hbf.1
          rw [RawByteCollisionTargets.pred_child]
          exact hchild
        exact before_trans tr hib hbf
    exact False.elim (hnot ((read_cut_iff tr frame input).mpr hbefore))

#print axioms read_cut_iff
#print axioms cut_consistent
#print axioms target_cases
#print axioms opening_read_of_input
#print axioms recover_at_first_commitment
end AspisR1.RawByteCutRecovery
end
