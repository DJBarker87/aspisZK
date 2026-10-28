import NCM_KeysLeaves
import NCM_TailModel
import NCM_OuterDirect

set_option autoImplicit false
noncomputable section
namespace AspisR1.NCM_Tree
open Aeneas Aeneas.Std Result MultiproofConeRef NCE_OpeningCuts
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def reset (s : Carrier) : Carrier := {s with scratch:=MultiproofConeSlotState.reset s.scratch}
def width (batch : Nat) : Usize := if batch = 0 then 10#usize else 12#usize

/-- Observation of the actual raw leaf interpreter followed by the actual
binary interpreter. The carried old prefix is removed ONLY from the output
observer; no digest is reissued or reconstructed from a completed trace. -/
def execute {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (keys : NCM_KeysLeaves.Keys) (leaf : NCM_LeafLoop.Ops)
    (count : NCM_CountCarrier.Ops) (padding : NCE_PaddingCuts.Body Carrier) (verifier : NCM_Tail.Verifier)
    (batch : Nat) (kind : Usize) (cap : Nat) (root : NCE_VerifierCuts.Digest) (nodes : Slice U8) (s : Carrier) :
    NCE_FirstFailure.Log × Bool × Carrier :=
  match NCM_KeysLeaves.run D hash keys leaf kind batch (width batch) (reset s) with
  | .ok (out,after) =>
    let reads := after.log.drop s.log.length
    match out with
    | none => (reads,false,after)
    | some _ =>
      let tail := eval H (NCM_Tail.run count padding verifier cap root nodes after)
      (reads++tail.1,tail.2)
  | _ => ([],false,s)

/-- Exact trace/result, immutable caller frame and SAME accepted scratch.
The rejected scratch is retained by the native observer but is not silently
identified with the cohort's discarded failure scratch. -/
def Agrees (H : Bytes → State) (source : NCE_FirstFailure.Log × Bool × Carrier)
    (target : Program Bytes State (Bool × reference.Scratch)) (before : Carrier) : Prop :=
  source.1 = (eval H target).1 ∧ source.2.1 = (eval H target).2.1 ∧
  source.2.2.prepared = before.prepared ∧ source.2.2.proof = before.proof ∧
  source.2.2.log = before.log++source.1 ∧
  (source.2.1 = true → source.2.2.scratch = (eval H target).2.2)

/-- Local physical tree composition. Every native hypothesis is a per-step
NCE fragment. The input domains are original proof/Prepared/root/slot facts,
not successful child returns, chosen counts, final scans or final logs. -/
theorem association {X : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State)
    (oracle : ∀ input, D.digest hash input = ok (MultiproofConePhysicalTransport.rawOracle H input))
    (keys : NCM_KeysLeaves.Keys)
    (keysZero : NCE_KeyProducerCuts.NCE_Native_KeysZero keys.create)
    (keysWrite : NCE_KeyCuts.NCE_Native_KeysWrite keys.write)
    (keysSort : NCE_SortCarrierCuts.NCE_Native_KeysSortCarrier keys.sort)
    (leaf : NCM_LeafLoop.Ops) (get : NCE_KeyReadCuts.NCE_Native_KeysRead leaf.get)
    (opening : NCE_OpeningCuts.NCE_Native_Opening leaf.reader)
    (leafCut : NCE_LeafCuts.NCE_Native_Leaf leaf.request leaf.post)
    (count : NCM_CountCarrier.Ops)
    (countZero : NCE_CountInitCuts.NCE_Native_CountZero count.create)
    (countCopy : NCE_CountInitCuts.NCE_Native_CountCopy count.copy)
    (countScan : NCE_CountCuts.NCE_Native_CountScan count.scan)
    (countStore : NCE_CountRowCuts.NCE_Native_CountCommit count.store)
    (countHeight : NCE_CountLevelCuts.NCE_Native_CountHeight count.height)
    (base : Port3_NativeBatchBody.Ops) (padding : NCE_PaddingCuts.Body Carrier)
    (paddingCut : NCE_PaddingCuts.NCE_Native_Padding (NCM_PaddingPredicate.predicate base D) padding)
    (verifier : NCM_Tail.Verifier) (row : NCE_CarrierEffects.NCE_Native_Row H verifier.node)
    (control : NCE_VerifierCuts.NCE_Native_Verifier verifier.entry verifier.exit verifier.finish)
    (admission : NCE_AdmissionCuts.NCE_Native_Admission verifier.pair verifier.range)
    (batch : Nat) (kind : Usize) (bb : batch < 2) (kb : kind.val < 3)
    (s : Carrier) (queries : ∀ j, j < 22 → s.prepared.queries.val[j]!.val < 262144)
    (size : s.proof.val.length = 57607) (parsed : OraclePortCompactDraft.Parsed)
    (wire : parsed.wire = MultiproofConeCanonical.bytesOf s.proof.val)
    (root : NCE_VerifierCuts.Digest) (rootValue : root = encodeState (OraclePortBatchDraft.committedRoot parsed kind.val))
    (nodes : Slice U8)
    (nodeSize : nodes.val.length = 32*OraclePortSelectedDraft.capacity (3*batch+kind.val))
    (cap : OraclePortSelectedDraft.capacity (3*batch+kind.val) ≤ 172) :
    Agrees H (execute D hash H keys leaf count padding verifier batch kind
      (OraclePortSelectedDraft.capacity (3*batch+kind.val)) root nodes s)
      (MultiproofConeSlotState.slotState parsed (Port4B_KeyInstall.queries s.prepared.queries) batch kind.val nodes s.scratch) s := by
  have countWidth : (width batch).val = (OraclePortSelectedDraft.batchPositions batch).length := by
    unfold width OraclePortSelectedDraft.batchPositions
    split <;> rfl
  obtain ⟨log,out,after,model,native,prepared,proof,reads,final⟩ := NCM_KeysLeaves.observation D hash H oracle keys keysZero keysWrite keysSort leaf get opening leafCut
    kind batch bb kb (reset s) queries (width batch) countWidth rfl size parsed wire
  simp only [reset] at native model prepared proof reads
  have newReads : after.log.drop s.log.length = log := by
    rw [reads]
    exact List.drop_left
  cases out with
  | none =>
    simp only [Agrees,execute,native,newReads,MultiproofConeSlotState.slotState,reset,eval_bind,model,eval,List.append_nil]
    exact ⟨True.intro,True.intro,prepared,proof,reads,by intro impossible;cases impossible⟩
  | some next =>
    have scratch := final next rfl
    have tail := NCM_Tail.association D (S2LeadInterface.multiproofDigest D) hash hash H oracle count countZero countCopy countScan countStore countHeight
      base padding paddingCut verifier row control admission _ cap root nodes nodeSize after
    rw [rootValue] at tail
    have tailModel := NCM_TailModel.observation H parsed batch kind.val nodes after
    have observed := tail.trans tailModel
    rw [scratch] at observed
    simp only [Agrees,execute,native,newReads,MultiproofConeSlotState.slotState,reset,eval_bind,model,rootValue,observed]
    refine ⟨True.intro,True.intro,prepared,proof,?_,?_⟩
    · rw [reads]
      simp only [reset,List.append_assoc]
    · intro accepted
      exact True.intro

#print axioms association
end AspisR1.NCM_Tree
end
