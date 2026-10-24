import Port10AUTH_Selected
import Port9OR_BatchLoop

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Leaves
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 CheckpointBytes5Effect
open Port4B_NativeLeaf Port4B_LeafStep MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical

/-- Accepted concrete emitted loop supplies the SAME canonical leaf fold and
its complete ordered reads, duplicates included. The terminal count/padding/
verifier observation remains an exact suffix, with its actual scratch. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (q : Fin 22 → Fin 262144) (batch : Nat) (kind lo n slot : Usize)
    (root : Digest) (keys : Array U64 16#usize)
    (outIdx : Port9OR_BatchStep.Indices) (outVal : Port9OR_BatchStep.Values)
    (ps : List Nat) (s : reference.Scratch) (pos : Usize) (fuel : Nat)
    (positions : ∀ p∈ps, p∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
    (loValue : lo.val=(if batch=0 then 0 else 10))
    (span : pos.val+ps.length=n.val) (small : n.val≤16)
    (room : s.n.val+ps.length≤16) (stream : Port4B_LeafLoop.KeyStream q batch kind.val keys pos ps)
    (run : erase D hash (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel s.idx s.val s.n pos)=
      ok (outIdx,outVal,some (.Ok ()))) :
    ∃ t remaining,
      eval H (MultiproofConeP6Batch.leaves MultiproofConeP6Batch.referenceLeaf parsed q kind.val ps s)=
        (ps.map (fun p => (OraclePortSelectedDraft.leaf parsed kind.val p,
          H (OraclePortSelectedDraft.leaf parsed kind.val p))),ok (some t)) ∧
      erase D hash (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys remaining t.idx t.val t.n n)=
        ok (outIdx,outVal,some (.Ok ())) ∧
      CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
        (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel s.idx s.val s.n pos)).1=
        ps.map (fun p => (OraclePortSelectedDraft.leaf parsed kind.val p,
          H (OraclePortSelectedDraft.leaf parsed kind.val p))) ++
        CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
          (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys remaining t.idx t.val t.n n)).1 := by
  induction ps generalizing s pos fuel with
  | nil =>
    have same : pos=n := UScalar.eq_of_val_eq (by simpa only [List.length_nil,Nat.add_zero] using span)
    exact ⟨s,fuel,rfl,by simpa only [same] using run,by simp only [List.map_nil,List.nil_append,same]⟩
  | cons selected rest ih =>
    cases fuel with
    | zero => cases run
    | succ fuel =>
      have more : pos<n := by change pos.val<n.val;simp only [List.length_cons] at span;omega
      have bound : s.n.val<16 := by simp only [List.length_cons] at room;omega
      have keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected) :=
        stream pos 0 (by simp) (by omega)
      have unfolded := run
      simp only [Port9OR_BatchLoop.code,erase_bind] at unfolded
      obtain ⟨step,stepRun,remainingRun⟩ := Port3_PushFrame.bind_success _ _ _ unfolded
      obtain ⟨view,viewRead,address,traced⟩ := Port10AUTH_Selected.iteration base D hash H oracle proof len parsed wire
        q batch selected kind lo n slot pos root keys s (positions selected (by simp)) loValue more bound keyRead step stepRun
      have stepValue := (Port9OR_Code.trace_value D hash _).symm.trans (congrArg Prod.snd traced)
      generalize choice : MultiproofConeLeafContent.next s (MultiproofConeLeafFold.key q kind.val selected)
        (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected))) bound=out at traced stepValue
      have stepEq := Result.ok.inj (stepRun.symm.trans stepValue)
      cases out with
      | none =>
        simp only [project] at stepEq
        subst step
        cases remainingRun
      | some t =>
        simp only [project] at stepEq
        subst step
        change erase D hash (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel t.idx t.val t.n
          (Usize.wrapping_add pos 1#usize))=ok (outIdx,outVal,some (.Ok ())) at remainingRun
        have advance := Port3_Wrapping.increment pos (by omega)
        have tb := MultiproofConeLeafFold.next_bound s _ _ bound t choice
        have tailStream : Port4B_LeafLoop.KeyStream q batch kind.val keys (Usize.wrapping_add pos 1#usize) rest := by
          intro cursor j hj value
          have read := stream cursor (j+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj) (by omega)
          simpa only [List.getElem_cons_succ] using read
        obtain ⟨final,terminalFuel,fold,terminal,logs⟩ := ih t (Usize.wrapping_add pos 1#usize) fuel
          (fun p hp => positions p (List.mem_cons_of_mem _ hp))
          (by simp only [List.length_cons] at span;omega) (by simp only [List.length_cons] at room;omega)
          tailStream remainingRun
        refine ⟨final,terminalFuel,?_,terminal,?_⟩
        · simp only [MultiproofConeP6Batch.leaves,eval_bind,MultiproofConeP6Batch.referenceLeaf,eval,
            MultiproofConeLeafContent.step_exact s _ _ bound,choice,fold,List.map_cons,List.cons_append,List.nil_append]
        · simp only [Port9OR_BatchLoop.code,Port10AUTH_Trace.trace_bind,traced,project]
          change CheckpointBytes5Inputs.observe ((Port4B_LeafCode.input kind view,
            encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected))) ::
            (Port9OR_Code.trace D hash (Port9OR_BatchLoop.code base D hash proof root kind lo n slot keys fuel
              t.idx t.val t.n (Usize.wrapping_add pos 1#usize))).1)=_
          have state : CheckpointBytesDigest.stateOf (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)))=
              H (OraclePortSelectedDraft.leaf parsed kind.val selected) := state_roundtrip _
          have addr : AspisR1DigestLogCarrier.flatten (Port4B_LeafCode.input kind view)=
              OraclePortSelectedDraft.leaf parsed kind.val selected := address
          simp only [CheckpointBytes5Inputs.observe,List.map_cons,addr,state,List.map_cons,List.cons_append]
          exact congrArg (List.cons _) logs

#print axioms accepted
end AspisR1.Port10AUTH_Leaves
end
