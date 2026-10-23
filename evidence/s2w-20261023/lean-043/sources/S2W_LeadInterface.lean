import CheckpointBytes5Decision
import MultiproofConeP6Frozen2Stage
import S7JoinQueryRows
import S8JoinFrozenScan

/-! Continuation 3 restatement of S2LeadInterface (new-module-only policy).
The historical module is retained unchanged. All consumer theorem statements
are reproduced on the revised record. The multiproof consumer retains its
existing P6Boundary, including that child boundary's own oracle law.

Caller inputs only. This record organizes still-open source obligations;
it does not discharge them. In particular it contains no execution result,
accepted observation, oracle log, or arithmetic-output equality. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W_LeadInterface
open Aeneas Aeneas.Std Result AspisR1Stage2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical OraclePortCompactDraft

/-- Relevant caller positions, in execution order, not oracle events.
Query positions summarize the ten/twelve-step blocks, not individual queries. -/
inductive Site where
  | tx1 | batch0 | query0 | save | tx2 | resume | batch1 | query1 | finish
  deriving DecidableEq

def Site.rank : Site → Nat
  | .tx1 => 0 | .batch0 => 1 | .query0 => 2 | .save => 3 | .tx2 => 4
  | .resume => 5 | .batch1 => 6 | .query1 => 7 | .finish => 8

/-- Full account input/frame carrier; field preservation includes metadata. -/
structure Account where
  key : Bytes
  owner : Bytes
  lamports : Nat
  data : Bytes
  signer : Bool
  writable : Bool
  executable : Bool
  rentEpoch : Nat

/-- Data supplied by a concrete caller refinement, never fabricated by compose.
The proof/public fields record retained input snapshots even at positions
where a callee does not consume both arguments. -/
structure Inputs (Observer : Type) where
  reached : Site → Prop
  clock : Site → Nat
  proof : Site → Slice U8
  publicInput : Site → Slice U8
  proofAccount : Site → Bytes
  checkpoint : Site → Slice U8
  nodes : Nat → Nat → Slice U8
  y1 : Slice U8
  observer : Site → Option Observer
  before : Site → Nat → Account
  after : Site → Nat → Account

/-- Only the admitted verifier adapter's TX1 account2 data write is allowed.
Pool settlement and CPI effects are a separate caller cone. -/
def dataWrite (s : Site) (a : Nat) : Bool := decide (s = .tx1 ∧ a = 2)

/-- The separate extraction has a distinct trait structure. Transport its
implementation fields explicitly; source adoption of this port remains P6. -/
def multiproofDigest {Hash : Type} (D : aspis_core.digest.Digest32 Hash) :
    MultiproofConeRef.aspis_core.digest.Digest32 Hash :=
  ⟨D.coremarkerCopyInst, D.digest⟩

/-- These are input-buffer identities, dispatch facts and account framing.
`oracle` is success-conditioned under continuation 3. Backend failure rejects
the run; no termination law is imposed on unused inputs. No arbitrary
Prop boundary, source output, log or observation equality is a field. -/
structure S2CallerFacts {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub savedBytes : Bytes) (parsed : Parsed) : Prop where
  proofBytes : ∀ s, c.reached s → bytesOf (c.proof s).val = stored
  publicBytes : ∀ s, c.reached s → bytesOf (c.publicInput s).val = pub
  proofSuffix : ∀ s, c.reached s → s = .tx1 ∨ s = .tx2 →
    c.proofAccount s = (c.proofAccount s).take 688 ++ stored
  proofLength : stored.length = 57607
  checkpointBytes : ∀ s, c.reached s → s = .save ∨ s = .tx2 ∨ s = .resume →
    bytesOf (c.checkpoint s).val = savedBytes
  checkpointLength : savedBytes.length = 1768
  nodeViews : ∀ b k, b < 2 → k < 3 → bytesOf (c.nodes b k).val =
    slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+k))
      (32*OraclePortSelectedDraft.capacity (3*b+k))
  y1Input : c.reached .tx1 → c.y1 = S8JoinFrozenScan.segment (c.proof .tx1) 7031 464
  observerNone : ∀ s, c.reached s → c.observer s = none
  reachedPrefix : ∀ s t, s.rank < t.rank → c.reached t → c.reached s
  callOrder : ∀ s t, s.rank < t.rank → c.reached s → c.reached t → c.clock s < c.clock t
  accountFrame : ∀ s, c.reached s → ∀ a, dataWrite s a = false → c.after s a = c.before s a
  writtenMetadata : c.reached .tx1 →
    {c.after .tx1 2 with data := (c.before .tx1 2).data} = c.before .tx1 2
  oracle : CheckpointBytes5Inputs.Oracle D hash H

/-- The SDK packet frames the 58295-byte account allocation, whereas the
lead consumes only the selected 57607-byte suffix. Use the actual range
result to cross this boundary; neither an address nor a length suffices. -/
theorem proof_suffix_bytes (account selected : Slice U8)
    (range : selected.val = (account.val.drop 688).take 57607) :
    bytesOf selected.val = slice (bytesOf account.val) 688 57607 := by
  rw [range]
  simp only [bytesOf, slice, List.map_take, List.map_drop]

/-- The revised field is exactly the checkpoint's success-conditioned law. -/
theorem checkpoint_oracle {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (H : Bytes → State)
    (law : CheckpointBytes5Inputs.Oracle D hash H) :
    CheckpointBytes5Inputs.Oracle D hash H := law

/-- Exact checkpoint caller premise, at either reached writer or reader site. -/
theorem checkpoint_binding {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub ck : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub ck parsed)
    (s : Site) (reached : c.reached s) :
    CheckpointBytes5Join.S2S10CallerBinding D hash H (c.proof s) (c.publicInput s) stored pub :=
  ⟨facts.proofBytes s reached, facts.publicBytes s reached,
    checkpoint_oracle D hash H facts.oracle⟩

/-- Compose S2 inputs with the existing S7 trace/initialization results.
The actual source PushTrace is supplied by the lead's S7 cone, NOT by S2.
The initial Progress conclusion refers only to the constructed initial state;
it is not silently identified with the resumed source accumulator. -/
theorem compose {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub ck : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub ck parsed)
    (save : c.reached .save) (resume : c.reached .resume)
    (old : S8OwnedP6Finish.Weights) (size : old.val.length = 64)
    (state : S7Kani2AccumulatorLoop.BatchedWeights) (sum : S7Kani3CallerTrace.Sum)
    (history : S7Kani3CallerTrace.PushTrace old state sum) :
    CheckpointBytes5Join.S2S10CallerBinding D hash H (c.proof .save) (c.publicInput .save) stored pub ∧
    CheckpointBytes5Join.S2S10CallerBinding D hash H (c.proof .resume) (c.publicInput .resume) stored pub ∧
    (∀ b k, b < 2 → k < 3 → bytesOf (c.nodes b k).val =
      slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+k))
        (32*OraclePortSelectedDraft.capacity (3*b+k))) ∧
    S7JoinRowsTrace.Progress 0 0
      (⟨S7Kani3CallerTrace.initialRaw old,0#usize⟩ : S7Kani2AccumulatorLoop.BatchedWeights) ∧
    S8Kani2CallerJoin.CallerInvariant state.raw old sum := by
  exact ⟨checkpoint_binding c D hash H stored pub ck parsed facts .save save,
    checkpoint_binding c D hash H stored pub ck parsed facts .resume resume,
    facts.nodeViews, S7JoinQueryRows.initial_progress old size,
    S7Kani3CallerTrace.reached_invariant old state sum history⟩

/-- Install all six physical slot views in the existing P6 batch join.
Local callback gates stay explicit; no whole-batch equality is assumed. -/
theorem multiproof_join {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub ck : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub ck parsed)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent)
    (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (multiproofDigest D) hash H binary occupied sibling leaf)
    (q : Fin 22 → Fin 262144) :
    (∀ s, (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q c.nodes 0 s)).2 = true →
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q c.nodes 0 s) =
        eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch0)) ∧
    (∀ s, (eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q c.nodes 1 s)).2 = true →
      eval H (MultiproofConeP6Frozen2Stage.sourceBatch occupied sibling leaf parsed q c.nodes 1 s) =
        eval H (OraclePortFrozen2.batch parsed q OraclePortFrozen2.batch1)) :=
  MultiproofConeP6Frozen2Stage.both_batches (multiproofDigest D) hash H binary occupied sibling leaf
    p6 parsed q c.nodes facts.nodeViews

/-- Exact y1 callee input, with accepted parser provenance kept separate. -/
theorem y1_join {Observer Hash : Type} (c : Inputs Observer)
    (D : aspis_core.digest.Digest32 Hash) (hash : Hash) (H : Bytes → State)
    (stored pub ck : Bytes) (parsed : Parsed)
    (facts : S2CallerFacts c D hash H stored pub ck parsed)
    (reached : c.reached .tx1) (tr : RawCutTranscriptRun.ErasedPrefix)
    (parser : OraclePortStoredParserC4.parseReached stored tr = some parsed) :
    S8OwnedP6.check_values_owned c.y1 = ok (.Ok ()) := by
  rw [facts.y1Input reached]
  apply S8JoinFrozenScan.parsed_y1 (c.proof .tx1) tr parsed
  change OraclePortStoredParserC4.parseReached (bytesOf (c.proof .tx1).val) tr = some parsed
  rw [facts.proofBytes .tx1 reached]
  exact parser

#print axioms proof_suffix_bytes
#print axioms checkpoint_oracle
#print axioms checkpoint_binding
#print axioms compose
#print axioms multiproof_join
#print axioms y1_join
end AspisR1.S2W_LeadInterface
end
