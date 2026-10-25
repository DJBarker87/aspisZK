import Port6AUTH_Prefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6AUTH_Probability
open FS FS2 FS2.Duplex R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound
open OraclePortStoredExperimentC4 OraclePortStoredAdmissionC4 OraclePortRuntimeBindingC7
open Port1_StoredCarrier RawRecordedOracleExtractionMassBin Port6AUTH_Prefix
attribute [local instance] Classical.propDecidable

/-- Sufficient SOURCE experiment interface, not a claim that its local source
obligations have all been instantiated. CleanAcceptedModel expands to terminal
checks and classifier no-hit for the actual extracted source record. It contains
no output/log equivalence or probability bound. Collision is charged ONCE on
this source log; prefix replay uses the unchanged Q+34 charged experiment. -/
theorem failure_bound (D : LiteralByteProtocol.Decoder) (rust : Verifier) (P : ByteProver) (Q : Nat)
    (hq : ∀ H : Bytes → State, (eval H P).1.length ≤ Q)
    (contains : ∀ H a, Read (eval H (Frozen2StartChargePrefix.charged D (lift P))).1 a →
      Read (eval H (source D rust P)).1 a)
    (budget : ∀ H, firstReads emptyTable (eval H (source D rust P)).1 ≤ Q+1161)
    (checks : CleanAcceptedModel D (source D rust P) (bad D P Q)) :
    lazyMean (source D rust P) emptyTable failureMass ≤
      BinCombinedMerkleCollision.kappa (Q+1161) +
        ((Q+34 : Nat) : ℚ)*PerAttemptEnvelope.B + 1/(2:ℚ)^126 := by
  have hc := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
    (Q+1161) (source D rust P) budget
  have hs := prefix_bound D rust P Q hq contains
  apply shared_oracle_failure_le_supplied_hit_bound D (source D rust P) (bad D P Q) checks
  calc
    lazyMean (source D rust P) emptyTable (fun run => indicator (bad D P Q run)) ≤
        lazyMean (source D rust P) emptyTable (fun run =>
          indicator (RecordedBinaryExperimentBin.binaryCollision (Q+1161) run) +
          indicator (prefixHit D P run)) :=
      AllAddressFiatShamir.lazyMean_mono_of_eval _ _ _ (fun _ => indicator_or_le _ _)
    _ = _ := lazyMean_add _ _ _ _
    _ ≤ _ := add_le_add hc hs

/-- The existing runtime carrier contract transports directly to the SOURCE
projection. Neither collision-free nor all-world source/model equality enters. -/
theorem runtime_transport (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : ByteProver) (runtime : Runtime)
    (binding : StoredCarrierBinding D rust (lift P) runtime) :
    deployedFailure runtime ≤ lazyMean (source D rust P) emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none => exact failure_nonnegative _
  | some run =>
    change failureMass (view run) ≤ failureMass (eval H (source D rust P))
    by_cases accepted : run.2.2=true
    · rw [binding H run hr accepted,source_eval]
    · have zero : failureMass (view run)=0 := by
        unfold failureMass
        simp only [view] at *
        simp [accepted,indicator,mean_const]
      rw [zero]
      exact failure_nonnegative _

#print axioms failure_bound
#print axioms runtime_transport
end AspisR1.Port6AUTH_Probability
end
