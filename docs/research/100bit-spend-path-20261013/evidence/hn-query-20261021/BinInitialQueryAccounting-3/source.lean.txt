import BinHonestQueryBudget
import DecoderFiniteStartSupport

set_option autoImplicit false
noncomputable section
namespace AspisR1.BinInitialQueryAccounting
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open RecordedBinaryExperimentBin RawCutProverCompiler DecodedFirstReadUnionBound
attribute [local instance] Classical.propDecidable

def CanonicalInitial (a : Bytes) : Prop :=
  ∃ (pub : LiteralTranscript.Public) (root : State), pub.tag = 2 ∧
    pub.pubBytes.length < 2^32 ∧
    a = CanonicalAddressEmbedding.toBytes (BinDecoderInitialStarts.initialAddress pub root)

def initialQueries (tr : List (Bytes × State)) : Nat :=
  ((tr.map Prod.fst).toFinset.filter CanonicalInitial).card

/-- Distinct selected inputs cannot outnumber issued queries. -/
theorem initial_le_queries (tr : List (Bytes × State)) : initialQueries tr ≤ tr.length := by
  unfold initialQueries
  exact (Finset.card_filter_le _ _).trans
    ((List.toFinset_card_le _).trans (by simp only [List.length_map]; exact le_rfl))

/-- Optional, explicit adversary restriction: an address it issues can
start this decoder only when it is a canonical initialization frame.
The query-normalised endpoint does NOT use this premise. -/
def InitialisationCharging (P : Prover) : Prop :=
  ∀ (H : Bytes → State) (q : Bytes × State), q ∈ (eval H P).1 →
    ∀ T : Table Bytes State, dec q.1 T ≠ none → CanonicalInitial q.1

theorem adversary_starts_le_initial (P : Prover)
    (hcharge : InitialisationCharging P) (H : Bytes → State) :
    decoderFirstReads dec emptyTable (eval H P).1 ≤ initialQueries (eval H P).1 := by
  let s := (((eval H P).1.map Prod.fst).toFinset.filter CanonicalInitial)
  have hb := DecoderFiniteStartSupport.starts_le_support dec emptyTable (eval H P).1 s (by
    intro q hq T hd
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨q,hq,rfl⟩),
      hcharge H q hq T hd⟩)
  simpa only [emptyTable, eq_self, Finset.filter_true, s, initialQueries] using hb

theorem recorded_le_initial_add (D : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (P : Prover) (hcharge : InitialisationCharging P) (H : Bytes → State) :
    decoderFirstReads dec emptyTable (eval H (recorded D d P)).1 ≤
      initialQueries (eval H P).1 + 34 := by
  change decoderFirstReads dec emptyTable
    (eval H (experiment (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P)
      (verifier D d))).1 ≤ _
  rw [RawCutCompilerDecoderStartLaw.decoderStarts_eq dec D d
    (BinCompiledRunWordStability.wordsFromRun D) P H,
    RawCutProverCompiler.experiment_eval, decoderFirstReads_append]
  exact Nat.add_le_add (adversary_starts_le_initial P hcharge H) (BinHonestQueryBudget.verifier_starts D d H _ _ _)

theorem adversary_initial_le_Q (P : Prover) (Q : Nat)
    (hq : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    initialQueries (eval H P).1 ≤ Q := (initial_le_queries _).trans (hq H)

#print axioms initial_le_queries
#print axioms adversary_starts_le_initial
#print axioms recorded_le_initial_add
#print axioms adversary_initial_le_Q
end AspisR1.BinInitialQueryAccounting
end
