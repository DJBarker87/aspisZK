import NCM_KeyStream

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_KeysLeaves
open Aeneas Aeneas.Std Result NCE_OpeningCuts NCE_KeyCuts NCE_KeyProducerCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

structure Keys where
  create : Carrier → Nat → Nat → KeyState
  write : KeyState → KeyState
  sort : NCE_SortCarrierCuts.Step

def run {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (keys : Keys) (leaf : NCM_LeafLoop.Ops) (kind : Usize) (batch : Nat) (n : Usize) (s : Carrier) :
    Result (Option MultiproofConeRef.reference.Scratch × Carrier) := do
  let raw := produce keys.create keys.write s batch kind.val
  let sorted ← NCE_SortCarrierCuts.sort keys.sort n.val raw.caller (array raw) 1#usize n
  NCM_LeafLoop.run D hash leaf kind batch n.val n.val sorted.1 0#usize sorted.2

/-- The producer, sort, getter and leaf traversal share ONE sorted witness,
ONE initial caller and every actual returned carrier. No final stream or
successful traversal is supplied as a hypothesis. -/
theorem observation {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (keys : Keys) (zero : NCE_Native_KeysZero keys.create) (write : NCE_Native_KeysWrite keys.write)
    (sort : NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier keys.sort)
    (leaf : NCM_LeafLoop.Ops) (get : NCE_KeyReadCuts.NCE_Native_KeysRead leaf.get)
    (reader : NCE_Native_Opening leaf.reader) (hashPost : NCE_LeafCuts.NCE_Native_Leaf leaf.request leaf.post)
    (kind : Usize) (batch : Nat) (bb : batch < 2) (kb : kind.val < 3)
    (s : Carrier) (queries : ∀ j, j < 22 → s.prepared.queries.val[j]!.val < 262144)
    (n : Usize) (count : n.val = (OraclePortSelectedDraft.batchPositions batch).length)
    (empty : s.scratch.n.val = 0) (size : s.proof.val.length = 57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = MultiproofConeCanonical.bytesOf s.proof.val) :
    ∃ log out after,
      eval H (MultiproofConeLeafFold.leaves parsed (Port4B_KeyInstall.queries s.prepared.queries) kind.val
        (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries s.prepared.queries) batch kind.val) s.scratch) = (log,ok out) ∧
      run D hash keys leaf kind batch n s = ok (out,after) ∧
      after.prepared = s.prepared ∧ after.proof = s.proof ∧ after.log = s.log++log ∧
      (∀ t, out = some t → after.scratch = t) := by
  obtain ⟨sorted,returned,stream⟩ := NCM_KeyStream.produced keys.create zero keys.write write keys.sort sort leaf.get get s batch kind.val bb kb queries n count
  have length : (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries s.prepared.queries) batch kind.val).length = n.val := by
    rw [count]
    simp only [OraclePortFrozenOrder.sortedPositions,List.length_mergeSort]
  have small := MultiproofConeLeafFrozen.sorted_length (Port4B_KeyInstall.queries s.prepared.queries) batch kind.val
  obtain ⟨log,out,after,model,native,prepared,proof,reads,final⟩ := NCM_LeafLoop.observation D hash H law leaf get reader hashPost kind batch n.val kb
    (by omega) (Port4B_KeyInstall.queries s.prepared.queries) parsed _ sorted 0#usize s
    (fun p mem => MultiproofConeKeyAdapters.sorted_member _ _ _ _ mem) stream
    (by simp only [show (0#usize).val=0 from rfl,Nat.zero_add,length])
    (by rw [empty];omega) size wire
  refine ⟨log,out,after,model,?_,prepared,proof,reads,final⟩
  simp only [run,returned,bind_tc_ok]
  simpa only [length] using native

#print axioms observation
end AspisR1.NCM_KeysLeaves
end
