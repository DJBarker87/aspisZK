import OracleDecisionFeasibilityCore
import AspisRec40ChargePrefix

/-! Aspis 40-row recorded experiment: the verifier with a terminal oracle
decision. Copies, for the 40-row protocol, of
`OracleDecisionFeasibilityCore.{verifierFrom, verifier, original}`,
`OracleDecisionFeasibilityBudget.{from_eval, verifier_eval}`,
`OracleDecisionFeasibilityCompiler.{verifierFrom_eq, verifier_eq, compiled,
eval_compiled, compiled_experiment_eval}`, `OracleDecisionPrereqStarts.annotated`
and `OraclePortExperiment.recorded`, and of `OraclePortSamplerPrefixDraft.split_trace`.

The decision type `OracleDecisionFeasibilityCore.Decision`
(`ErasedPrefix → ErasedMessage → Program Bytes State Bool`) and `onBytes` are
reused unchanged: they do not mention the row count. Changed: the row bound
33 → 40 (rows 0 to 39 are sampled, the terminal decision reads the prefix of
40 rounds and message 40), and R1's protocol → `AspisRows40.Protocol.protocol`. -/
set_option autoImplicit false
noncomputable section
namespace AspisRec40.Decision
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 RawCutTranscriptRun
open RawCutProverCompiler (Public Proof Prover RunView experiment experiment_eval)
open CanonicalCutEnrichedTranscript (Words enrichPrefix enrichMessage)
open OracleDecisionFeasibilityCore (Decision onBytes)

abbrev pr (D : LiteralByteProtocol.Decoder) := AspisRows40.Protocol.protocol D

/-- Copy of `OracleDecisionFeasibilityCore.verifierFrom`, 33 → 40. -/
def verifierFrom (D : LiteralByteProtocol.Decoder) (dO : Decision) (pf : Proof) :
    Nat → LiteralTranscript.Prefix → Program Bytes State Bool
  | 0, p => onBytes dO p (pf 40)
  | n + 1, p => bind (LiteralByteSampler.samp (40 - (n + 1)) p
      (pf (40 - (n + 1)))).toProgram fun c =>
        verifierFrom D dO pf n (p.ext (pf (40 - (n + 1))) c)

def verifier (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (pub : Public) (pf : Proof) : Program Bytes State Bool :=
  verifierFrom D dO pf 40 (emptyPrefix pub)

def original (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) :=
  experiment P (verifier D dO)

/-- Copy of `OracleDecisionFeasibilityBudget.from_eval`, 33 → 40. -/
theorem from_eval (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof) :
    ∀ n, n ≤ 40 →
      eval H (verifierFrom D dO pf n ((pr D).transcript H pub pf (40 - n))) =
      let final := eval H (onBytes dO ((pr D).transcript H pub pf 40) (pf 40))
      ((((List.range n).map fun j => (eval H
        ((pr D).chain H pub pf (40 - n + j)).toProgram).1).flatten
        ++ final.1), final.2) := by
  intro n
  induction n with
  | zero => intro _; simp [verifierFrom]
  | succ n ih =>
    intro hn
    have hi : 40 - (n + 1) + 1 = 40 - n := by omega
    simp only [verifierFrom]
    rw [eval_bind]
    dsimp only
    have hstep :
        ((pr D).transcript H pub pf (40 - (n + 1))).ext
          (pf (40 - (n + 1)))
          (eval H (LiteralByteSampler.samp (40 - (n + 1))
            ((pr D).transcript H pub pf (40 - (n + 1)))
            (pf (40 - (n + 1)))).toProgram).2 =
          (pr D).transcript H pub pf (40 - n) := by
      rw [← hi]; rfl
    rw [hstep, ih (by omega)]
    dsimp only
    refine Prod.ext ?_ rfl
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, List.flatten_cons,
      List.append_assoc, Protocol.chain]
    congr 1
    congr 1
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    have hj : 40 - (n + 1) + (j + 1) = 40 - n + j := by omega
    rw [hj]

/-- Copy of `OracleDecisionFeasibilityBudget.verifier_eval`, 33 → 40. -/
theorem verifier_eval (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (H : Bytes → State) (pub : Public) (pf : Proof) :
    eval H (verifier D dO pub pf) =
      let final := eval H (onBytes dO ((pr D).transcript H pub pf 40) (pf 40))
      ((((List.range 40).map fun j => (eval H
        ((pr D).chain H pub pf j).toProgram).1).flatten
        ++ final.1), final.2) := by
  exact from_eval D dO H pub pf 40 le_rfl

/-- Copy of `OracleDecisionFeasibilityCompiler.verifierFrom_eq`, 33 → 40. -/
theorem verifierFrom_eq (D : LiteralByteProtocol.Decoder)
    (d : Decision) (w : Words)
    (pf : LiteralProtocol.Proof) (n : Nat) (P : LiteralTranscript.Prefix) :
    verifierFrom D d (proof w pf) n (enrichPrefix w P) = verifierFrom D d pf n P := by
  induction n generalizing P with
  | zero =>
      change onBytes d (enrichPrefix w P) (enrichMessage w (pf 40)) = onBytes d P (pf 40)
      simp only [onBytes, CanonicalCutEnrichedTranscript.erasePrefix_enrich,
        CanonicalCutEnrichedTranscript.erase_enrichMessage]
  | succ n ih =>
      change bind (LiteralByteSampler.samp (40 - (n+1)) (enrichPrefix w P)
          (enrichMessage w (pf (40 - (n+1))))).toProgram
          (fun c => verifierFrom D d (proof w pf) n
            ((enrichPrefix w P).ext (enrichMessage w (pf (40 - (n+1)))) c)) =
        bind (LiteralByteSampler.samp (40 - (n+1)) P (pf (40 - (n+1)))).toProgram
          (fun c => verifierFrom D d pf n (P.ext (pf (40 - (n+1))) c))
      rw [byte_sampler_eq]
      congr 1
      funext c
      rw [← prefix_ext]
      exact ih _

theorem verifier_eq (D : LiteralByteProtocol.Decoder) (d : Decision) (w : Words)
    (pub : LiteralTranscript.Public) (pf : LiteralProtocol.Proof) :
    verifier D d pub (proof w pf) = verifier D d pub pf :=
  verifierFrom_eq D d w pf 40 (FS.emptyPrefix pub)

/-- Copy of `OracleDecisionFeasibilityCompiler.compiled`. -/
def compiled (D : LiteralByteProtocol.Decoder) (d : Decision)
    (buildWords : RunView → Words) (P : Prover) : Prover :=
  bind (OracleProgramRecording.record (experiment P (verifier D d))) fun v =>
    Program.done (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)

theorem eval_compiled (D : LiteralByteProtocol.Decoder) (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (compiled D d buildWords P) =
      let v := eval H (experiment P (verifier D d))
      (v.1, (v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2)) := by
  rw [compiled, eval_bind, OracleProgramRecording.eval_record]
  simp [eval]

/-- Copy of `OracleDecisionFeasibilityCompiler.compiled_experiment_eval`. -/
theorem compiled_experiment_eval (D : LiteralByteProtocol.Decoder) (d : Decision)
    (buildWords : RunView → Words) (P : Prover) (H : Bytes → State) :
    eval H (experiment (compiled D d buildWords P) (verifier D d)) =
      let v := eval H (experiment P (verifier D d))
      (v.1 ++ (eval H (verifier D d v.2.1.1 v.2.1.2)).1,
        ((v.2.1.1, RawCutTranscriptRun.proof (buildWords v) v.2.1.2), v.2.2)) := by
  rw [RawCutProverCompiler.experiment_eval, eval_compiled]
  dsimp only
  have he (pub : Public) (pf : Proof) (w : Words) :
      verifier D d pub (RawCutTranscriptRun.proof w pf) = verifier D d pub pf :=
    verifier_eq D d w pub pf
  rw [he]
  have hb : (eval H (verifier D d
      (eval H (experiment P (verifier D d))).2.1.1
      (eval H (experiment P (verifier D d))).2.1.2)).2 =
      (eval H (experiment P (verifier D d))).2.2 := by
    rw [RawCutProverCompiler.experiment_eval]
  rw [hb]

/-- Copy of `OracleDecisionPrereqStarts.annotated`. -/
def annotated (D : LiteralByteProtocol.Decoder) (dO : Decision)
    (words : RunView → Words) (P : Prover) :=
  experiment (compiled D dO words P) (verifier D dO)

/-- Copy of `OraclePortExperiment.recorded`. -/
abbrev recorded (D : LiteralByteProtocol.Decoder) (dO : Decision) (P : Prover) :=
  annotated D dO (BinCompiledRunWordStability.wordsFromRun D) P

/-- Copy of `OraclePortSamplerPrefixDraft.base`: the 40-row verifier with the
always-true decision. -/
abbrev base (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) : RunView :=
  eval H (experiment P (AspisRows40.Starts.verifier D (fun _ _ => true)))

/-- Copy of `OraclePortSamplerPrefixDraft.terminal`, 33 → 40. -/
abbrev terminal (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :=
  (eval H (onBytes d ((pr D).transcript H (eval H P).2.1 (eval H P).2.2 40)
    ((eval H P).2.2 40))).1

/-- Copy of `OraclePortSamplerPrefixDraft.split_trace`: the full verifier's trace
is the always-true verifier's trace followed by the terminal decision's reads. -/
theorem split_trace (D : LiteralByteProtocol.Decoder) (d : Decision) (P : Prover)
    (H : Bytes → State) :
    (eval H (original D d P)).1 = (base D P H).1 ++ terminal D d P H := by
  rw [original, RawCutProverCompiler.experiment_eval, verifier_eval]
  unfold base
  rw [RawCutProverCompiler.experiment_eval, AspisRows40.Starts.verifier, FS2.verifier_eval]
  simp only [List.append_assoc]
  rfl

#print axioms from_eval
#print axioms verifier_eval
#print axioms verifierFrom_eq
#print axioms verifier_eq
#print axioms eval_compiled
#print axioms compiled_experiment_eval
#print axioms split_trace

end AspisRec40.Decision
end
