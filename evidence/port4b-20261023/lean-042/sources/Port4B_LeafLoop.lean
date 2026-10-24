import Port4B_LeafCut

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_LeafLoop
open Aeneas Aeneas.Std Result ControlFlow
open Port3_NativeBatchCalls (Indices Values)
open MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

/-- A physical sorted-prefix carrier equation, at every remaining index.
It is independent of whether the batch succeeds. -/
def KeyStream (q : Fin 22 → Fin 262144) (batch kind : Nat)
    (keys : Array U64 16#usize) (pos : Usize) (ps : List Nat) : Prop :=
  ∀ (cursor : Usize) (j : Nat) (bound : j<ps.length), cursor.val=pos.val+j →
    Array.index_usize keys cursor=ok (MultiproofConeSortOrder.packed q batch kind ps[j])

/-- Accepted native leaf traversal forces the P6 fold to succeed on the SAME
scratch. Its exact ordered reads are the sorted openings, duplicates included.
The actual native terminal call is retained for count/padding/verifier transport. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (law : ∀ input, D.digest hash input=ok (MultiproofConePhysicalTransport.rawOracle H input))
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch : Nat) (kind lo n slot : Usize)
    (root : Array U8 32#usize) (keys : Array U64 16#usize)
    (outIdx : Indices) (outVal : Values)
    (ps : List Nat) (s : reference.Scratch) (pos : Usize)
    (positions : ∀ p∈ps, p∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
    (loValue : lo.val=(if batch=0 then 0 else 10))
    (span : pos.val+ps.length=n.val) (small : n.val≤16)
    (room : s.n.val+ps.length≤16) (stream : KeyStream q batch kind.val keys pos ps)
    (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
      (Port3_BatchStd.install (Port4B_LeafInstall.install base)) D proof root kind s.idx s.val
      hash lo n slot keys s.n pos = ok (outIdx,outVal,some (.Ok ()))) :
    ∃ t,
      eval H (MultiproofConeP6Batch.leaves MultiproofConeP6Batch.referenceLeaf parsed q kind.val ps s)=
        (ps.map (fun p => (OraclePortSelectedDraft.leaf parsed kind.val p,
          H (OraclePortSelectedDraft.leaf parsed kind.val p))),ok (some t)) ∧
      Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
        (Port3_BatchStd.install (Port4B_LeafInstall.install base)) D proof root kind t.idx t.val
        hash lo n slot keys t.n n = ok (outIdx,outVal,some (.Ok ())) := by
  induction ps generalizing s pos with
  | nil =>
    have same : pos=n := UScalar.eq_of_val_eq (by simpa using span)
    exact ⟨s,rfl,by simpa only [same] using run⟩
  | cons selected rest ih =>
    have more : pos<n := by change pos.val<n.val;simp only [List.length_cons] at span;omega
    have bound : s.n.val<16 := by simp only [List.length_cons] at room;omega
    have headRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected) :=
      stream pos 0 (by simp) (by omega)
    obtain ⟨view,viewRead,address,reads,body⟩ := Port4B_LeafCut.iteration base D hash H law
      proof len parsed wire q batch selected kind lo n slot pos root keys s
      (positions selected (by simp)) loValue more bound headRead []
    unfold Port3_NativeBatchBody.verifier.candidate.batch_tree_loop at run
    rw [Aeneas.Std.loop.eq_def] at run
    simp only [Aeneas.Std.uncurry,body,MultiproofConeP6Batch.referenceLeaf,eval,
      MultiproofConeLeafContent.step_exact s _ _ bound,bind_tc_ok] at run
    generalize choice : MultiproofConeLeafContent.next s (MultiproofConeLeafFold.key q kind.val selected)
      (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected))) bound=out at run
    cases out with
    | none => cases run
    | some t =>
      have advance := Port3_Wrapping.increment pos (by omega)
      have tb := MultiproofConeLeafFold.next_bound s _ _ bound t choice
      have tailStream : KeyStream q batch kind.val keys (Usize.wrapping_add pos 1#usize) rest := by
        intro cursor j hj value
        have read := stream cursor (j+1) (by simpa using Nat.succ_lt_succ hj) (by omega)
        simpa only [List.getElem_cons_succ] using read
      change Port3_NativeBatchBody.verifier.candidate.batch_tree_loop
        (Port3_BatchStd.install (Port4B_LeafInstall.install base)) D proof root kind t.idx t.val
        hash lo n slot keys t.n (Usize.wrapping_add pos 1#usize)=_ at run
      obtain ⟨final,fold,terminal⟩ := ih t (Usize.wrapping_add pos 1#usize)
        (fun p hp => positions p (List.mem_cons_of_mem _ hp))
        (by simp only [List.length_cons] at span;omega) (by simp only [List.length_cons] at room;omega)
        tailStream run
      refine ⟨final,?_,terminal⟩
      simp only [MultiproofConeP6Batch.leaves,eval_bind,MultiproofConeP6Batch.referenceLeaf,eval,
        MultiproofConeLeafContent.step_exact s _ _ bound,choice,fold,List.map_cons,List.cons_append,List.nil_append]

#print axioms accepted
end AspisR1.Port4B_LeafLoop
end
