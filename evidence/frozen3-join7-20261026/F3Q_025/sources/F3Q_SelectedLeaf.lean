import Port4B_KeyDecode
import F3Q_LeafActive

set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_SelectedLeaf
open Aeneas Aeneas.Std Result ControlFlow
open Port4B_NativeLeaf Port4B_LeafStep MultiproofConeRef
open CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

theorem iteration {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch selected : Nat) (kind lo n slot pos : Usize)
    (root : Array U8 32#usize) (keys : Array U64 16#usize) (s : reference.Scratch)
    (mem : selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
    (loValue : lo.val=(if batch=0 then 0 else 10)) (more : pos<n) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected)) :
    eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root kind hash
      lo n slot keys s.idx s.val s.n pos))=
      ([(OraclePortSelectedDraft.leaf parsed kind.val selected,H (OraclePortSelectedDraft.leaf parsed kind.val selected))],
       (do let out ← reference.leaf_step s (MultiproofConeLeafFold.key q kind.val selected)
          (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)))
           ok (Port4B_LeafStep.project s (Usize.wrapping_add pos 1#usize) out))) := by
  have member := MultiproofConeKeyAdapters.sorted_member q batch kind.val selected mem
  have decoded := Port4B_KeyDecode.packed q batch kind.val selected member lo loValue
  have rebased : (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected)).val=
      (if batch=0 then 0 else 10)+(MultiproofConeSortOrder.packed q batch kind.val selected).val%256 :=
    decoded.2.trans (MultiproofConeKeyAdapters.packed_opening q batch kind.val selected member).symm
  obtain ⟨view,viewRead,size,content⟩ := Port4B_Opening.selected proof len parsed wire q batch kind.val selected mem
    (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected)) rebased
  have address : flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val selected := by
    rw [Port4B_LeafCode.address,content,MultiproofConeOpeningAdapters.leaf_address]
  have indexEq : decodedIndex (MultiproofConeSortOrder.packed q batch kind.val selected)=
      MultiproofConeLeafFold.key q kind.val selected := by
    apply UScalar.eq_of_val_eq
    exact decoded.1
  have step := F3Q_LeafActive.step_eval D hash H proof root kind lo n slot pos keys s
    (MultiproofConeSortOrder.packed q batch kind.val selected) view more keyRead viewRead size
  rw [address,indexEq,Port4B_LeafStep.reference_post s _ _ _ room] at step
  exact step

#print axioms iteration
end AspisR1.F3Q_SelectedLeaf
end
