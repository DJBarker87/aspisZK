import BinDecoderInitialStarts
import DecoderStartCounting

set_option autoImplicit false
noncomputable section
namespace AspisR1.BinDecoderStartCounterexample
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding RecordedBinaryExperimentBin BinDecoderInitialStarts
open RawCutProverCompiler RawCutTranscriptRun DecodedFirstReadUnionBound

def candidatePublic (i : Fin 34) : LiteralTranscript.Public :=
  { pubBytes := [⟨i.val, by omega⟩], initFits := by change 76 ≤ 131072; decide, tag := 2 }

def address (i : Fin 34) : Bytes := toBytes (initialAddress (candidatePublic i) default)

theorem address_injective : Function.Injective address := by
  intro i j he
  have hs := congrArg (fun a => RawFullPublicSelection.select a emptyTable) he
  have sel (k : Fin 34) : RawFullPublicSelection.select (address k) emptyTable = some (candidatePublic k) := by
    rw [address, RawFullPublicSelection.select, RawPublicSelectionLift.of_canonical]
    exact FullPublicSelection.initial _ _ _ (by change 1 < 2^32; decide) rfl _
  rw [sel i, sel j] at hs
  have hb := congrArg (fun p : LiteralTranscript.Public => p.pubBytes) (Option.some.inj hs)
  have hv : i.val = j.val := by simpa only [candidatePublic, List.cons.injEq, Fin.mk.injEq, and_true] using hb
  exact Fin.ext hv

def startTrace (H : Bytes → State) : List (Bytes × State) :=
  (List.finRange 34).map (fun i => (address i, H (address i)))

theorem prefix_count (H : Bytes → State) : decoderFirstReads dec emptyTable (startTrace H) = 34 := by
  have hn : ((startTrace H).map Prod.fst).Nodup := by
    simpa only [startTrace, List.map_map, Function.comp_def] using
      (List.nodup_finRange 34).map address_injective
  have hh := DecoderStartCounting.all_fresh dec emptyTable (startTrace H) hn
    (by intro q hq; rfl) (by
      intro q hq T
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
      exact recognizes_initial (candidatePublic i) default (by change 1 < 2^32; decide) rfl T)
  simpa only [startTrace, List.length_map, List.length_finRange] using hh

/-- Fixed finite oracle program: queries these addresses and then runs P.
It is independent of H; the supplied dummy answers are ignored by readTrace. -/
def adversary (P : Prover) : Prover :=
  bind (RawBoundedProgram.readTrace (startTrace (fun _ => default)) ()) (fun _ => P)

theorem adversary_eval (P : Prover) (H : Bytes → State) :
    eval H (adversary P) = ((startTrace H) ++ (eval H P).1, (eval H P).2) := by
  have hr : RawBoundedProgram.readTrace (startTrace (fun _ => (default : State))) () =
      RawBoundedProgram.readTrace (startTrace H) () := by
    unfold startTrace
    generalize List.finRange 34 = xs
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [List.map_cons, RawBoundedProgram.readTrace]
      rw [ih]
  rw [adversary, hr, eval_bind, RawBoundedProgram.eval_readTrace H _ () (by
    intro q hq
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    rfl)]

/-- The extra oracle queries change neither the returned proof/public statement nor
acceptance under a fixed oracle. In particular they can precede an accepted
continuation; this obstruction is not confined to rejecting experiments. -/
theorem original_output (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    (eval H (original D d (adversary P))).2 = (eval H (original D d P)).2 := by
  change (eval H (experiment (adversary P) (verifier D d))).2 =
    (eval H (experiment P (verifier D d))).2
  rw [RawCutProverCompiler.experiment_eval, RawCutProverCompiler.experiment_eval, adversary_eval]

theorem recorded_acceptance (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    (eval H (recorded D d (adversary P))).2.2 =
      (eval H (original D d P)).2.2 := by
  exact (RawCutProverCompiler.public_and_acceptance D d
    (BinCompiledRunWordStability.wordsFromRun D) (adversary P) H).2.trans
      (congrArg Prod.snd (original_output D d P H))

/-- Expose the prefix as a list identity before applying the counting
lemmas; no decoder is reduced on this concrete finite log. -/
theorem recorded_trace (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    (eval H (recorded D d (adversary P))).1 = startTrace H ++
      ((eval H P).1 ++ (eval H (verifier D d (eval H P).2.1 (eval H P).2.2)).1 ++
        (eval H (verifier D d (eval H P).2.1 (eval H P).2.2)).1) := by
  change (eval H (experiment (compiled D d (BinCompiledRunWordStability.wordsFromRun D)
    (adversary P)) (verifier D d))).1 = _
  rw [RawCutProverCompiler.compiled_experiment_eval]
  simp only [RawCutProverCompiler.experiment_eval, adversary_eval, List.append_assoc]

/-- Counterexample inside the exact binary recorded experiment, for every
protocol decoder, decision map, continuation prover and oracle. -/
theorem recorded_more_than_33 (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (H : Bytes → State) :
    33 < decoderFirstReads dec emptyTable (eval H (recorded D d (adversary P))).1 := by
  have h := DecoderStartCounting.append_lower dec emptyTable (startTrace H)
    ((eval H P).1 ++ (eval H (verifier D d (eval H P).2.1 (eval H P).2.2)).1 ++
      (eval H (verifier D d (eval H P).2.1 (eval H P).2.2)).1)
  have he := congrArg (decoderFirstReads dec emptyTable) (recorded_trace D d P H)
  have hn := prefix_count H
  exact lt_of_lt_of_le (lt_of_lt_of_eq (by decide : 33 < 34) hn.symm)
    (le_of_le_of_eq h he.symm)

#print axioms address_injective
#print axioms prefix_count
#print axioms adversary_eval
#print axioms original_output
#print axioms recorded_acceptance
#print axioms recorded_trace
#print axioms recorded_more_than_33
end AspisR1.BinDecoderStartCounterexample
end
