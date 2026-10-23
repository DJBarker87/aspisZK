import Port4B_KeyDecode

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_LeafCut
open Aeneas Aeneas.Std Result ControlFlow
open Port4B_NativeLeaf Port4B_LeafStep MultiproofConeRef
open CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

/-- One ACTUAL native iteration, with the physical key/opening/hash and
P6 insertion joined. The only read assumption is one actual array access
from the sorted key prefix; source effects are not a batch-equality premise. -/
theorem iteration (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input=ok (MultiproofConePhysicalTransport.rawOracle H input))
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch selected : Nat) (kind lo n slot pos : Usize)
    (root : Array U8 32#usize) (keys : Array U64 16#usize) (s : reference.Scratch)
    (mem : selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
    (loValue : lo.val=(if batch=0 then 0 else 10)) (more : pos<n) (room : s.n.val<16)
    (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected))
    (before : Log) :
    ∃ view,
      (Port4B_LeafInstall.install base).op2 proof
        (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected))=ok view ∧
      flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val selected ∧
      run D hash (Port4B_LeafCode.code kind view) before=
        ok (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)),
          before++[(Port4B_LeafCode.input kind view,
            encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)))]) ∧
      Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
        (Port3_BatchStd.install (Port4B_LeafInstall.install base)) D proof root kind hash lo n slot
        keys s.idx s.val s.n pos =
        (do let out ← (eval H (MultiproofConeP6Batch.referenceLeaf parsed q kind.val selected s)).2
            ok (project s (Usize.wrapping_add pos 1#usize) out)) := by
  have member := MultiproofConeKeyAdapters.sorted_member q batch kind.val selected mem
  have decoded := Port4B_KeyDecode.packed q batch kind.val selected member lo loValue
  have rebased : (openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected)).val=
      (if batch=0 then 0 else 10)+(MultiproofConeSortOrder.packed q batch kind.val selected).val%256 :=
    decoded.2.trans (MultiproofConeKeyAdapters.packed_opening q batch kind.val selected member).symm
  obtain ⟨view,viewRead,leafRead,reads,address⟩ := Port4B_LeafInstall.selected_call
    base D hash H law proof len parsed wire q batch selected kind _ mem rebased before
  refine ⟨view,viewRead,address,reads,?_⟩
  have indexEq : decodedIndex (MultiproofConeSortOrder.packed q batch kind.val selected)=
      MultiproofConeLeafFold.key q kind.val selected := by
    apply UScalar.eq_of_val_eq
    exact decoded.1
  have native := Port4B_NativeLeaf.step (Port4B_LeafInstall.install base) D hash proof root
    kind lo n slot pos keys s _ view _ more room keyRead viewRead leafRead
  rw [indexEq] at native
  exact native

#print axioms iteration
end AspisR1.Port4B_LeafCut
end
