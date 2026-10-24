import Port10AUTH_Leaf

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Selected
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port4B_NativeLeaf Port4B_LeafStep MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

/-- A reached emitted leaf iteration has exactly the canonical leaf's ordered
read, before its actual duplicate comparison. Success of the primitive is
DERIVED from the iteration, not imposed on unrelated inputs. -/
theorem iteration (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch selected : Nat) (kind lo n slot pos : Usize)
    (root : Digest) (keys : Array U64 16#usize) (s : reference.Scratch)
    (mem : selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
    (loValue : lo.val=(if batch=0 then 0 else 10)) (more : pos<n) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected))
    (out : ControlFlow Port9OR_BatchStep.Next Port9OR_BatchStep.Out)
    (accepted : erase D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n pos)=ok out) :
    ∃ view, (Port9OR_BatchStep.ops base).op2 proof
        (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected))=ok view ∧
      flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val selected ∧
      Port9OR_Code.trace D hash (Port9OR_BatchStep.body base D proof root kind hash lo n slot keys s.idx s.val s.n pos)=
        ([(Port4B_LeafCode.input kind view,encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)))],
          ok (project s (Usize.wrapping_add pos 1#usize)
            (MultiproofConeLeafContent.next s (MultiproofConeLeafFold.key q kind.val selected)
              (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected))) room))) := by
  have member := MultiproofConeKeyAdapters.sorted_member q batch kind.val selected mem
  have decoded := Port4B_KeyDecode.packed q batch kind.val selected member lo loValue
  have rebased : (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected)).val=
      (if batch=0 then 0 else 10)+(MultiproofConeSortOrder.packed q batch kind.val selected).val%256 :=
    decoded.2.trans (MultiproofConeKeyAdapters.packed_opening q batch kind.val selected member).symm
  obtain ⟨view,read,size,content⟩ := Port4B_Opening.selected proof len parsed wire q batch kind.val selected mem _ rebased
  have viewRead : (Port9OR_BatchStep.ops base).op2 proof
      (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected))=ok view := read
  have address : flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val selected := by
    rw [Port4B_LeafCode.address,content,MultiproofConeOpeningAdapters.leaf_address]
  obtain ⟨digest,hashed,postRun,trace⟩ := Port10AUTH_Leaf.accepted_trace base D hash proof root kind lo n slot s.n pos
    keys s.idx s.val _ view more keyRead viewRead size out accepted
  have decodedDigest := oracle _ digest hashed
  rw [address] at decodedDigest
  have digestEq : digest=encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)) := by
    have eq := congrArg encodeState decodedDigest
    exact (MultiproofConePhysicalViews.array_roundtrip digest).symm.trans eq
  have indexEq : decodedIndex (MultiproofConeSortOrder.packed q batch kind.val selected)=
      MultiproofConeLeafFold.key q kind.val selected := UScalar.eq_of_val_eq decoded.1
  rw [digestEq,indexEq,post_exact s _ _ _ room] at postRun
  have output := Result.ok.inj postRun
  exact ⟨view,viewRead,address,by simpa only [digestEq,← output] using trace⟩

#print axioms iteration
end AspisR1.Port10AUTH_Selected
end
