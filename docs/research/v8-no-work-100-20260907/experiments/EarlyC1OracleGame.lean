import EarlyC1OracleMachine
import AuthenticatedEarlyC1Targets
import AspisFormal.K1.V7Tag73K12Merkle208PrefixProjection

/-! Whole-domain early-C1 target hits in an actual finite lazy-oracle model.
The continuation observes FULL 256-bit answers. We lift the 208-bit target
set using the existing exact 2^48 fibre theorem, retaining cached calls,
fresh-budget exhaustion, and arbitrary later input selection. -/
set_option autoImplicit false
set_option maxRecDepth 150
set_option maxHeartbeats 500000
namespace AspisV8.EarlyC1OracleGame
open AspisV8.EarlyC1OracleMachine AspisV8.AuthenticatedEarlyC1Prefix
open AspisV8.AuthenticatedEarlyC1Targets AspisPool.V7MerkleQueryGrammar
open AspisK1.V7Tag73AdaptiveLazyOracle AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier

noncomputable section

abbrev FullPrefix := List (RawHashInput × RuntimeDigest256)

def initialCache : FullPrefix → RawHashInput → Option RuntimeDigest256
  | [], _ => none
  | (key, answer) :: rest, input =>
      if key = input then some answer else initialCache rest input

def merklePrefix (records : FullPrefix) : AnswerPrefix :=
  records.map fun record => (record.1, runtimeDigest256PrefixToMerkleDigest record.2)

theorem merklePrefix_raw (records : FullPrefix) :
    rawPrefix (merklePrefix records) = records.map Prod.fst := by
  simp only [rawPrefix, merklePrefix, List.map_map]
  rfl

theorem initialCache_none_iff (records : FullPrefix) (key : RawHashInput) :
    initialCache records key = none ↔ key ∉ records.map Prod.fst := by
  induction records with
  | nil => simp [initialCache]
  | cons record rest ih =>
      rcases record with ⟨input, answer⟩
      by_cases same : input = key
      · subst input
        simp [initialCache]
      · have different := Ne.symm same
        simpa only [initialCache, if_neg same, List.map_cons, List.mem_cons,
          different, false_or] using ih

def fullCap : Nat := 262144 * 2 ^ 48

def fullTargets (records : FullPrefix) (root : Digest208) : Finset RuntimeDigest256 :=
  deployedPrefixTargetPreimage (allTargets (merklePrefix records) root)

theorem fullTargets_card_le (records : FullPrefix) (root : Digest208) :
    (fullTargets records root).card ≤ fullCap :=
  deployed_prefix_target_preimage_card_le _ (allTargets_card_le (merklePrefix records) root)

def gameRun {steps : Nat} (records : FullPrefix)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat)
    (tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length) :=
  run fullCap strategy Q (initialCache records) tape

def gameLog {steps : Nat} (records : FullPrefix)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat)
    (tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length) : List RawHashInput :=
  records.map Prod.fst ++ (gameRun records strategy Q tape).calls.map Prod.fst

def gameView {steps : Nat} (records : FullPrefix)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat)
    (tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length)
    (input : RawHashInput) : Digest208 :=
  runtimeDigest256PrefixToMerkleDigest
    (((gameRun records strategy Q tape).cache input).getD (fun _ => 0))

def gameEvent {steps : Nat} (records : FullPrefix) (root : Digest208)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat)
    (tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length) : Prop :=
  WholeDomainLaterHit (gameView records strategy Q tape) (merklePrefix records)
    root (gameLog records strategy Q tape)

/-- This inclusion is derived from the actual cache/log semantics. An input
in the final log but absent from the initial prefix has a recorded answer
preserved in the final cache; unknown-input default zero cannot cause it. -/
theorem game_event_implies_new_target_event {steps : Nat}
    (records : FullPrefix) (root : Digest208)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat)
    (tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length)
    (bad : gameEvent records root strategy Q tape) :
    NewTargetEvent (fullTargets records root) fullCap strategy Q (initialCache records) tape := by
  classical
  obtain ⟨input, inLog, fresh, target⟩ := bad
  have absent : input ∉ records.map Prod.fst := by simpa only [merklePrefix_raw] using fresh
  have inCalls : input ∈ (gameRun records strategy Q tape).calls.map Prod.fst :=
    (List.mem_append.mp inLog).resolve_left absent
  obtain ⟨record, recorded, keyExact⟩ := List.mem_map.mp inCalls
  rcases record with ⟨key, answer⟩
  change key = input at keyExact
  subst key
  have cached := run_calls_cached fullCap strategy Q (initialCache records) tape
    input answer recorded
  refine ⟨input, answer, (initialCache_none_iff records input).mpr absent, cached, ?_⟩
  have projected : runtimeDigest256PrefixToMerkleDigest answer ∈
      allTargets (merklePrefix records) root := by
    simpa only [gameView, gameRun, cached, Option.getD_some] using target
  simpa only [fullTargets, deployedPrefixTargetPreimage,
    Finset.mem_filter, Finset.mem_univ, true_and] using projected

def gameCount {steps : Nat} (records : FullPrefix) (root : Digest208)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat) : Nat := by
  classical
  exact Fintype.card {tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length //
    gameEvent records root strategy Q tape}

theorem game_count_le {steps : Nat} (records : FullPrefix) (root : Digest208)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat) :
    gameCount records root strategy Q ≤ Q * fullCap * (2 ^ 256) ^ (steps - 1) := by
  classical
  let injection :
      {tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length //
        gameEvent records root strategy Q tape} →
      {tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length //
        NewTargetEvent (fullTargets records root) fullCap strategy Q (initialCache records) tape} :=
    fun tape => ⟨tape.1, game_event_implies_new_target_event records root strategy Q tape.1 tape.2⟩
  have injective : Function.Injective injection := by
    intro left right equal
    apply Subtype.ext
    exact congrArg
      (fun tape : {tape : FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length //
        NewTargetEvent (fullTargets records root) fullCap strategy Q (initialCache records) tape}
        => tape.1) equal
  have countBound := new_target_event_count_le (fullTargets records root) fullCap
    (fullTargets_card_le records root) strategy Q (initialCache records)
  rw [deployed_digest_256_cardinality] at countBound
  exact (Fintype.card_le_of_injective injection injective).trans countBound

/-- Literal uniform-tape probability, preserving the harmless zero-step
convention. For steps>0 the rational RHS simplifies to Q*262144/2^208.
This is a model theorem, not the Rust/FS source-event connection. -/
theorem game_probability_le_exact_count {steps : Nat}
    (records : FullPrefix) (root : Digest208)
    (strategy : Strategy RawHashInput RuntimeDigest256 steps) (Q : Nat) :
    (uniformDigestFreshTape (caps fullCap steps).length).toOuterMeasure
        {tape | gameEvent records root strategy Q tape} ≤
      ((Q * fullCap * (2 ^ 256) ^ (steps - 1) : Nat) : ENNReal) /
        (((2 : ENNReal) ^ 256) ^ steps) := by
  classical
  unfold uniformDigestFreshTape
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  change (gameCount records root strategy Q : ENNReal) /
    (Fintype.card (FreshAnswerTape RuntimeDigest256 (caps fullCap steps).length) : ENNReal) ≤ _
  rw [fresh_answer_tape_card, deployed_digest_256_cardinality, caps_length]
  have castPower : ((2 ^ 256 : Nat) : ENNReal) = (2 : ENNReal) ^ 256 := by norm_cast
  rw [Nat.cast_pow, castPower]
  apply ENNReal.div_le_div_right
  exact_mod_cast game_count_le records root strategy Q

#print axioms initialCache_none_iff
#print axioms fullTargets_card_le
#print axioms game_event_implies_new_target_event
#print axioms game_count_le
#print axioms game_probability_le_exact_count
end
end AspisV8.EarlyC1OracleGame
