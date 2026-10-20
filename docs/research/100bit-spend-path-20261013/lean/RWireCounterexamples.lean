import RWireCompletion
import R19BudgetOriginalReads
import AspisV8R19.OracleFiniteSupport

set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireCounterexamples
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open RawCutProverCompiler RawCutTranscriptRun RecordedBinaryExperimentBin
attribute [local irreducible] BinCompiledRunWordStability.wordsFromRun RawCutProverCompiler.compiled
  RawCutProverCompiler.verifier RawCutProverCompiler.experiment

theorem recorded_eq (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :
    recorded D d P = experiment
      (compiled D d (BinCompiledRunWordStability.wordsFromRun D) P) (verifier D d) := by
  unfold RecordedBinaryExperimentBin.recorded AcceptedAdaptiveFiatShamir.experiment
    RawCutProverCompiler.experiment
  rfl

/-- A bound below one supplies an actual collision-free oracle, symbolically. -/
theorem exists_clean {O : Type} (p : Program Bytes State O) (Q : Nat)
    (hQ : ∀ H, firstReads emptyTable (eval H p).1 ≤ Q)
    (hlt : BinCombinedMerkleCollision.kappa Q < 1) :
    ∃ H : Bytes → State, ¬ BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q (eval H p) := by
  by_contra hn
  have hall : ∀ H : Bytes → State, BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q (eval H p) := by
    simpa only [not_exists, not_not] using hn
  have hm : lazyMean p emptyTable (fun run => indicator (BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q run)) = 1 := by
    change lazyMean p (fun _ => none) _ = 1
    rw [← AspisV8R19.OracleFiniteSupport.finite_support_oracle_law p
      (AspisV8R19.OracleFiniteSupport.support p) (fun _ h => h) default]
    have he : (fun H => indicator (BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q
        (eval (AspisV8R19.OracleFiniteSupport.extend
          (AspisV8R19.OracleFiniteSupport.support p) H default) p))) = (fun _ => (1 : ℚ)) := by
      funext H
      simp only [indicator, if_pos (hall _)]
    rw [he, mean_const]
  have hb := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv Q p hQ
  change lazyMean p emptyTable (fun run => indicator (BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q run)) ≤ _ at hb
  rw [hm] at hb
  exact (not_le_of_gt hlt) hb

def badProver (tag : Fin 256) : Prover :=
  .done (⟨[], by decide, tag⟩, fun _ => .initial default default)

theorem accepted (D : LiteralByteProtocol.Decoder) (tag : Fin 256) (H : Bytes → State) :
    FS2.accepts (eval H (recorded D (fun _ _ => true) (badProver tag))) := by
  rw [recorded_eq]
  have hv (pub : Public) (pf : Proof) :
      (eval H (verifier D (fun _ _ => true) pub pf)).2 = true := by
    unfold RawCutProverCompiler.verifier
    rw [FS2.verifier_eval]
    rfl
  have ha : FS2.accepts (eval H (original D (fun _ _ => true) (badProver tag))) := by
    change (eval H (experiment (badProver tag) (verifier D (fun _ _ => true)))).2.2 = true
    rw [RawCutProverCompiler.experiment_eval]
    exact hv _ _
  have he := public_and_acceptance D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (badProver tag) H
  exact he.2.trans ha

theorem bad_public (D : LiteralByteProtocol.Decoder) (tag : Fin 256) (H : Bytes → State) :
    (eval H (recorded D (fun _ _ => true) (badProver tag))).2.1.1.tag = tag := by
  rw [recorded_eq]
  have he := public_and_acceptance D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (badProver tag) H
  have hpub : (eval H (original D (fun _ _ => true) (badProver tag))).2.1.1.tag = tag := by
    change (eval H (experiment (badProver tag) (verifier D (fun _ _ => true)))).2.1.1.tag = tag
    rw [RawCutProverCompiler.experiment_eval]
    rfl
  exact (congrArg (fun pub : Public => pub.tag) he.1).trans hpub

theorem bad_initial (D : LiteralByteProtocol.Decoder) (tag : Fin 256) (H : Bytes → State)
    (n : Nat) : ∃ word, (eval H (recorded D (fun _ _ => true) (badProver tag))).2.1.2 n =
      .initial default word := by
  rw [recorded_eq]
  let orig := eval H (original D (fun _ _ => true) (badProver tag))
  have hp : orig.2.1.2 n = .initial default default := by
    change (eval H (experiment (badProver tag) (verifier D (fun _ _ => true)))).2.1.2 n = _
    rw [RawCutProverCompiler.experiment_eval]
    rfl
  have he := compiled_experiment_eval D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (badProver tag) H
  have hepf := congrArg (fun run : RunView => run.2.1.2 n) he
  change (eval H (experiment (compiled D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (badProver tag))
    (verifier D (fun _ _ => true)))).2.1.2 n =
    CanonicalCutEnrichedTranscript.enrichMessage
      (BinCompiledRunWordStability.wordsFromRun D orig) (orig.2.1.2 n) at hepf
  rw [hp] at hepf
  exact ⟨_, hepf⟩

theorem bad_budget (D : LiteralByteProtocol.Decoder) (tag : Fin 256) :
    ∀ H, firstReads emptyTable
      (eval H (recorded D (fun _ _ => true) (badProver tag))).1 ≤ 1161 := by
  intro H
  rw [recorded_eq]
  have he := RawCutProverCompiler.firstReads_eq D (fun _ _ => true)
    (BinCompiledRunWordStability.wordsFromRun D) (badProver tag) H
  have hb := R19BudgetOriginalReads.original_reads D (fun _ _ => true) (badProver tag) 0
    (by intro H; exact Nat.le_refl 0) H
  exact he.trans_le hb

/-- Actual accepted, collision-free recorded execution with a nonselected tag.
This disproves unconditional completion over arbitrary d and P. -/
theorem non_two_accepted_counterexample (D : LiteralByteProtocol.Decoder) :
    ∃ H : Bytes → State,
      FS2.accepts (eval H (recorded D (fun _ _ => true) (badProver 0))) ∧
      ¬ binaryCollision 1161 (eval H (recorded D (fun _ _ => true) (badProver 0))) ∧
      ¬ BinaryCompletion D (fun _ _ => true) (badProver 0) 1161 := by
  obtain ⟨H,hout⟩ := exists_clean _ 1161 (bad_budget D 0)
    (by norm_num [BinCombinedMerkleCollision.kappa])
  refine ⟨H, accepted D 0 H, hout, ?_⟩
  intro hc
  obtain ⟨word,hw⟩ := bad_initial D 0 H 0
  have ht := RWireCompletion.initialTag_of_completion D _ _ _ hc H hout (accepted D 0 H)
    (by rw [hw]; trivial)
  rw [bad_public] at ht
  exact (by decide : (0 : Fin 256) ≠ 2) ht

/-- Two different rounds cannot share a first cell when exact completion holds. -/
theorem distinct_first_cells (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hc : BinaryCompletion D d P Q) (H : Bytes → State)
    (hout : ¬ binaryCollision Q (eval H (recorded D d P)))
    (ha : FS2.accepts (eval H (recorded D d P))) (n m : Nat) (a : Bytes)
    (hn : n < 33) (hm : m < 33)
    (hfn : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n) = some a)
    (hfm : firstCell ((LiteralByteProtocol.protocol D).chain H
      (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 m) = some a) : n = m := by
  obtain ⟨s,ps,g,hd,hf⟩ := hc H hout ha n a hn hfn
  obtain ⟨s',ps',g',hd',hf'⟩ := hc H hout ha m a hm hfm
  have he := Option.some.inj (hd.symm.trans hd')
  cases he
  have ho := Option.some.inj (hf.symm.trans hf')
  have hr := congrArg (fun out : RawLiteralDecoderDensity.LiteralOutput => out.1.round) ho
  simpa only [FS2.transcript_round] using hr

/-- The residual tag law is strictly weaker: a tag-2 malformed prover meets
it, but repeated invalid-schedule first cells make full completion impossible. -/
theorem strict_weakening (D : LiteralByteProtocol.Decoder) :
    RWireCompletion.InitialTag D (fun _ _ => true) (badProver 2) 1161 ∧
      ¬ BinaryCompletion D (fun _ _ => true) (badProver 2) 1161 := by
  refine ⟨?_, ?_⟩
  · intro H _ _ _
    exact bad_public D 2 H
  · intro hc
    obtain ⟨H,hout⟩ := exists_clean _ 1161 (bad_budget D 2)
      (by norm_num [BinCombinedMerkleCollision.kappa])
    have first (n : Nat) (hn : 0 < n) :
        firstCell ((LiteralByteProtocol.protocol D).chain H
          (eval H (recorded D (fun _ _ => true) (badProver 2))).2.1.1
          (eval H (recorded D (fun _ _ => true) (badProver 2))).2.1.2 n) =
          some (squeezeA SelectedTranscriptParams.params SelectedTranscriptParams.params.iv).toBytes := by
      obtain ⟨word, hw⟩ := bad_initial D 2 H n
      change firstCell (LiteralByteSampler.samp n _ _) = _
      change firstCell (LiteralByteSampler.samp n _
        ((eval H (recorded D (fun _ _ => true) (badProver 2))).2.1.2 n)) = _
      rw [hw]
      cases n with
      | zero => omega
      | succ n => rfl
    have h := distinct_first_cells D _ _ _ hc H hout (accepted D 2 H) 1 2 _
      (by decide) (by decide) (first 1 (by decide)) (first 2 (by decide))
    omega

#print axioms recorded_eq
#print axioms exists_clean
#print axioms accepted
#print axioms bad_public
#print axioms bad_initial
#print axioms bad_budget
#print axioms non_two_accepted_counterexample
#print axioms distinct_first_cells
#print axioms strict_weakening
end AspisR1.RWireCounterexamples
end
