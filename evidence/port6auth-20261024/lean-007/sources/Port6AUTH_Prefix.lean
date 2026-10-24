import Port1_CanonicalJoin
import Frozen2StartChargeProbability
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Prefix
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open AspisV8R19.OracleResampling
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier RawRecordedOracleExtractionMassBin
attribute [local instance] Classical.propDecidable

/-- Actual two source annotation passes on byte-indexed submissions; only the
stored carrier is erased AFTER execution, preserving every ordered query. -/
def source (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) : Experiment :=
  bind (annotatedWith D rust (canon (lift P))) fun v => .done ((v.1.statement,v.1.proof),v.2)

theorem source_eval (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (H : Bytes → State) :
    eval H (source D rust P)=view (eval H (annotatedWith D rust (canon (lift P)))) := by
  simp only [source,eval_bind,eval,List.append_nil,view]

abbrev prefixHit (D : LiteralByteProtocol.Decoder) (P : ByteProver) :=
  Frozen2StartChargeClean.prefixHit D (lift P)

def bad (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (run : RawCutProverCompiler.RunView) : Prop :=
  RecordedBinaryExperimentBin.binaryCollision (Q+1161) run ∨ prefixHit D P run

/-- An actual source log containing all charged reads replays the identical
adaptive charged computation, including prover history, duplicate reads and
answers. No permutation or frozen decision equality is required. -/
theorem recovered (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a) (H : Bytes → State) :
    Frozen2StartChargePrefix.recovered D (lift P) (eval H (source D rust P))=
      eval H (Frozen2StartChargePrefix.charged D (lift P)) := by
  apply OracleProgramReplay.eval_oracleOf H _ _ (FS.eval_consistent H _)
  exact contains H

/-- Source prefix-hit mass is measured under the full SOURCE probability law.
The prover is never fixed or conditioned on acceptance or collision exclusion. -/
theorem hit_mass (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a) :
    lazyMean (source D rust P) emptyTable (fun run => indicator (prefixHit D P run))=
      lazyMean (Frozen2StartChargePrefix.charged D (lift P)) emptyTable (fun run =>
        indicator (hitsChain3 RecordedBinaryExperimentBin.dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)) := by
  apply OracleProgramLawExt.lazyMean_eq_of_eval
  intro H
  unfold prefixHit Frozen2StartChargeClean.prefixHit
  rw [recovered D rust P contains H]

theorem prefix_bound (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a) :
    lazyMean (source D rust P) emptyTable (fun run => indicator (prefixHit D P run)) ≤
      ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B := by
  rw [hit_mass D rust P contains]
  apply RawAdaptiveClassifierStartBound.shared_hit_mass_le_starts
    RawFullPublicSelection.select LiteralTableWordChoiceBin.choose
  apply Frozen2StartChargePrefix.starts
  intro H
  simpa only [lift_eval] using hq H

#print axioms source_eval
#print axioms recovered
#print axioms hit_mass
#print axioms prefix_bound
end AspisR1.Port6AUTH_Prefix
end
