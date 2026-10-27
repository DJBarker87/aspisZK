import RPz7_F3U_RuntimeMass
import RPz7_F3T_Combined
import RPz7_F3T_RuntimeBound
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_ConditionalBound
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.CausalFirstHitUnionBound
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Runtime F3U_CollisionJoin
open RawRecordedOracleExtractionMassBin

theorem bound {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (P : ByteProver) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (hashv : SdkC_Source.Parts → Aeneas.Std.Result SdkC_Source.Digest)
    (runtime : Runtime) (bad : Exception)
    (join : Join c D (F3T_Installed.source c hashv) bad)
    (binding : StoredCarrierBinding c D (F3T_Installed.source c hashv) P runtime)
    (account : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (accountBudget : ∀ H,firstReads emptyTable (eval H account).1≤Q+1921)
    (association : ∀ H : Bytes → State,bad H (eval H P).2.publicBytes (eval H P).2.stored →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
        (eval H (Hiq_RecordedJoint.program account project select))) :
    F3T_RuntimeBound.failureModel runtime≤F3T_Numeric.total Q := by
  have transport := F3U_RuntimeMass.charge c D _ (F3T_Installed.physical c hashv) bad join P runtime binding
    (Hiq_RecordedJoint.program account project select)
    (fun v=>BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) v) association
  have lifted : ∀ H : Bytes → State,(eval H (lift c P)).1.length≤Q := by
    intro H;rw [lift_eval];exact queries H
  have model := F3T_ModelClaims.failure_bound D (lift c P) Q lifted
  have accountBound := F3T_AccountCharge.bound account project select Q accountBudget
  have combined := add_le_add model accountBound
  rw [F3T_Combined.arithmetic] at combined
  change F3T_Runtime.deployedFailure runtime≤_+F3T_AccountCharge.mass account project select Q at transport
  unfold F3T_RuntimeBound.failureModel F3T_ModelClaims.failure at *
  linarith

#print axioms bound
end AspisR1.F3U_ConditionalBound
end
