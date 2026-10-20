import BinCombinedMerkleCollision
import BinMultiproof

/-! Same-root, same-index binding outside the single five-reader event.
The symbolic depth covers the 18-level commitment; no tree is enumerated.
Mirrors Merkle32Leaf.lean:48 and RawByteCutRecovery.lean:115-116. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.BinOpeningBinding
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open BinMerkle32Path BinMerkle32Leaf

theorem openings_agree
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (depth index : Nat) (tag : BinMerkle32Path.Byte)
    (leftPath rightPath : Path (BinMultiproof.slots depth index))
    (leftPacked leftSalt rightPacked rightSalt : Bytes)
    (hwidth : leftPacked.length = rightPacked.length)
    (root : State)
    (hl : foldPath H leftPath (H (leafInput tag leftPacked leftSalt)) = root)
    (hr : foldPath H rightPath (H (leafInput tag rightPacked rightSalt)) = root)
    (hlogLeft : ∀ a ∈ fullTrace H leftPath (leafInput tag leftPacked leftSalt), Read tr a)
    (hlogRight : ∀ a ∈ fullTrace H rightPath (leafInput tag rightPacked rightSalt), Read tr a) :
    leftPacked = rightPacked ∧ leftSalt = rightSalt := by
  rcases leaf_path_binding tag leftPath rightPath leftPacked leftSalt rightPacked rightSalt
      hwidth (hl.trans hr.symm) with hagree | hcollision
  · exact hagree
  · obtain ⟨a, ha, b, hb, hne, heq⟩ := hcollision
    exact False.elim (AllAddressCollisionTrace.outputs_injective iv
      BinRawByteCollisionTargets.pred H tr Q hcons hQ hout a b
      (hlogLeft a ha) (hlogRight b hb) hne heq)

#print axioms openings_agree
end AspisR1.BinOpeningBinding
end
