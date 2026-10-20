import BinHonestQueryBudget

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

/-- Optional adversary restriction. The all-row causal decoder can recognise
noninitial starts too, so no unconditional charging to initial frames is assumed.
The query-normalised endpoint does NOT use this premise. -/
def InitialisationCharging (P : Prover) : Prop :=
  ∀ H : Bytes → State, decoderFirstReads dec emptyTable (eval H P).1 ≤
    initialQueries (eval H P).1

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
  exact Nat.add_le_add (hcharge H) (BinHonestQueryBudget.verifier_starts D d H _ _ _)

theorem adversary_initial_le_Q (P : Prover) (Q : Nat)
    (hq : DecoderQueryAccounting.AdversaryQueries P Q) (H : Bytes → State) :
    initialQueries (eval H P).1 ≤ Q := (initial_le_queries _).trans (hq H)

#print axioms initial_le_queries
#print axioms recorded_le_initial_add
#print axioms adversary_initial_le_Q
end AspisR1.BinInitialQueryAccounting
end
