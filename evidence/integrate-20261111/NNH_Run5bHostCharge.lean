import NNH_Run5bRecorderFixed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bHostCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open NNH_Run5bCtx NNH_Run5bRecorderFixed
open FS FS2

/-- SAME event for every oracle outcome; no realized-pair condition. -/
theorem event_fixed
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (fx : Fixed) (H anchor : Bytes → State) :
 NNH_Run5bExec.ERec copy fx H ↔
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
  (eval H (fixedProgram copy fx anchor)) := by
 change BinRawByteCollisionTargets.event _ _ (eval H (program copy fx H)) ↔ _
 rw [fixed copy fx H anchor]

/-- The single already-adopted accountLoss charge at that very fixed program.
This is a bound on E_rec; actual Failure inclusion is a separate open gate. -/
theorem bound
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (fx : Fixed) (anchor : Bytes → State) :
 lazyMean (fixedProgram copy fx anchor) emptyTable
  (fun v => AspisV8R19.CausalFirstHitUnionBound.indicator
    (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965) v))
 ≤ F3T_Numeric.accountLoss (fx.Q0+fx.Q1) :=
 NNH_RecordedCharge.bound copy (NNH_Run5bRecorderFixed.base fx anchor) fx.indexError fx.reservation
  (DGP_HostDigest.hashvInst anchor) fx.a (fx.Q0+fx.Q1)

#print axioms event_fixed
#print axioms bound
end AspisR1.NNH_Run5bHostCharge
end
