import FSQuerySchedule
import FSOptionBranch
import FSV7SelectedBodyScript

/-! No caller-supplied query schedule: absorb this body's final256 bytes and
third nonce, run the block-accurate sampler, then use its typed returned
positions in the same-body Merkle suffix. Sampler failure and Merkle abort
retain their actual states.

The incoming transcript must still be produced through the real preceding
semantic/OOD/relation/alpha0 phases. This module does not pretend a root cut
alone produces that digest. The raw-byte/canonical-field serialization bridge
and literal Rust parser/check order are separate source obligations. No ROM
law, post-hoc ideal strategy, or global accepted-payment theorem is claimed. -/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV7SampledBodyScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSQuerySampler FSQuerySchedule
open FSV7PrefixBridge FSV7SelectedBodyScript
open AspisPool.V7MerkleQueryGrammar AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerkleOpeningBinding
open AspisV8.MinimalMultiproofPaths AspisV8.SelectedWireMerkleRun

/-- Source query_schedule labels: V6_FINAL256=53, GRIND_NONCE=5.
Canonical profile ranges: fields441..696 (4096 bytes), nonce2 at11220.
The nonce is absorbed with all its selection powers; no work credit exists. -/
def beforeQueries (tape : Tape) (before : Transcript)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) : Transcript :=
  absorb tape (absorb tape before 53 (decode ((body.drop 7056).take 4096)))
    5 (decode ((body.drop 11220).take 8))

def positionsOf (schedule : Schedule) : Fin 22 → Position :=
  fun i => ⟨(schedule.positions i).val, (schedule.positions i).isLt⟩

def sampledBody (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) :
    Option (Schedule × Option OrderedRawQueryLog) × Oracle :=
  let queryPrefix := beforeQueries tape before body
  let sampled := reference tape 8 queryPrefix [] 0
  FSOptionBranch.branch sampled.1 (none, sampled.2.oracle) (fun returned success =>
    let schedule := from_success tape queryPrefix returned success
    let checked := run tape (selectedScript cuts (positionsOf schedule) body) sampled.2.oracle
    (some (schedule, checked.1), checked.2))

theorem before_queries_valid (tape : Tape) (before : Transcript)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (valid : FSFirstFresh.ValidHistory before.oracle) :
    FSFirstFresh.ValidHistory (beforeQueries tape before body).oracle :=
  absorb_valid tape _ 5 _ (absorb_valid tape before 53 _ valid)

/-- Eliminate the dependent sampler match once, preserving its constructed
schedule proof. Proof irrelevance equates only proofs of the SAME sampled
list equation; no completed schedule is substituted independently. -/
theorem sampled_body_some (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (returned : List Nat)
    (sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 = some returned) :
    sampledBody tape before cuts body =
      let schedule := from_success tape (beforeQueries tape before body) returned sample
      let checked := run tape (selectedScript cuts (positionsOf schedule) body)
        (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle
      (some (schedule, checked.1), checked.2) := by
  unfold sampledBody
  dsimp only
  simpa only using FSOptionBranch.some_branch
    (reference tape 8 (beforeQueries tape before body) [] 0).1
    (none, (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle)
    (fun actual actualSample =>
      let schedule := from_success tape (beforeQueries tape before body) actual actualSample
      let checked := run tape (selectedScript cuts (positionsOf schedule) body)
        (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle
      (some (schedule, checked.1), checked.2)) returned sample

theorem sampled_body_none (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte)
    (sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 = none) :
    sampledBody tape before cuts body =
      (none, (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle) := by
  unfold sampledBody
  dsimp only
  simpa only using FSOptionBranch.none_branch
    (reference tape 8 (beforeQueries tape before body) [] 0).1
    (none, (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle)
    (fun actual actualSample =>
      let schedule := from_success tape (beforeQueries tape before body) actual actualSample
      let checked := run tape (selectedScript cuts (positionsOf schedule) body)
        (reference tape 8 (beforeQueries tape before body) [] 0).2.oracle
      (some (schedule, checked.1), checked.2)) sample

/-- Returned query positions come from the actual sampler execution; their
distinctness/range and all Merkle interfaces are constructed. The only
history invariant assumed is that of the incoming pre-query state. -/
theorem sampled_body_constructs (tape : Tape) (before : Transcript) (cuts : RootCuts)
    (body : List AspisPool.V7MerkleQueryGrammar.Byte) (schedule : Schedule) (trace : OrderedRawQueryLog)
    (valid : FSFirstFresh.ValidHistory before.oracle)
    (success : (sampledBody tape before cuts body).1 = some (schedule, some trace)) :
    Function.Injective (positionsOf schedule) ∧
    (∃ returned, (reference tape 8 (beforeQueries tape before body) [] 0).1 = some returned ∧
      ∀ i, ((positionsOf schedule) i).val = returned.getD i.val 0) ∧
    ∃ merkle : SuccessfulMerkleRun (oldView (sampledBody tape before cuts body).2)
        (positionsOf schedule) body,
      merkle.trace = trace ∧ merkle.wire.roots 0 = root208 cuts.c1 ∧
      merkle.wire.roots 1 = root208 cuts.c2 ∧
      TraceIncludedInLog (leafLog (positionsOf schedule) (wireRecords merkle.wire) ++ merkle.trace)
        (oldLog (sampledBody tape before cuts body).2) := by
  cases sample : (reference tape 8 (beforeQueries tape before body) [] 0).1 with
  | none =>
    rw [sampled_body_none tape before cuts body sample] at success
    contradiction
  | some returned =>
    rw [sampled_body_some tape before cuts body returned sample] at success ⊢
    have both := Option.some.inj success
    have same := congrArg Prod.fst both
    change from_success tape (beforeQueries tape before body) returned sample = schedule at same
    subst schedule
    have merkleSuccess := congrArg Prod.snd both
    have afterSampling := queries_valid tape 8
      (beforeQueries tape before body).digest (beforeQueries tape before body).oracle [] 0
      (before_queries_valid tape before body valid)
    constructor
    · intro i j equal
      apply (from_success tape (beforeQueries tape before body) returned sample).distinct
      apply Fin.ext
      exact congrArg Fin.val equal
    constructor
    · refine ⟨returned, by simp only [sample], ?_⟩
      intro i
      have count := (reference_success tape 8 (beforeQueries tape before body) [] returned 0 empty_valid sample).2
      have bound : i.val < returned.length := by omega
      change returned[i.val]'bound = returned.getD i.val 0
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound, Option.getD_some]
    · exact selected_constructs tape cuts _ body _ trace afterSampling.coherent merkleSuccess

#print sampled_body_constructs
#print axioms before_queries_valid
#print axioms sampled_body_some
#print axioms sampled_body_none
#print axioms sampled_body_constructs
end AspisV8Completion.FSV7SampledBodyScript
