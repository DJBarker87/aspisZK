import NNH8_Exec
import NNH_Run5bFullSpace
set_option autoImplicit false
noncomputable section
/-! Run 7 (G0 FINAL): the SAME-recorder single charge (NNH_Run5bRecorderFixed, HostCharge,
FullSpace) restated at the corrected seed. O1 = NNH_DigestSyntaxTransport.o1 and
O2 = NNQ_HostDigest.o2 are the delivered seed-generic theorems, applied at the NOC seed. -/
namespace AspisR1.NNH8_RecorderFixed
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx

def env (fx : Fixed) (H : Bytes → State) :=
 DGP_HostDigest.envInst H fx.pda fx.clock fx.reservation

def base (fx : Fixed) (H : Bytes → State) :=
 IDa_Deployed.deployedConfiguration
  (NNH_Tx2Configuration.select (NNH_CorrectConfiguration.residual (NNH8_Exec.seed (env fx H)) (env fx H)) (env fx H))
  fx.indexError fx.reservation

def program
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (fx : Fixed) (H : Bytes → State) :=
 NNH_RecordedCharge.recorder copy (base fx H) fx.indexError fx.reservation
  (DGP_HostDigest.hashvInst H) fx.a (fx.Q0+fx.Q1)

/-- One fixed program for the complete oracle/randomness experiment. Anchor
is arbitrary fixed DATA, not an assumption about the sampled oracle. -/
def fixedProgram
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (fx : Fixed) (anchor : Bytes → State) := program copy fx anchor

def digest0 : S2Z.Oracle.Digest := Array.repeat 32#usize 0#u8

theorem fixed
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (fx : Fixed) (H anchor : Bytes → State) : program copy fx H = fixedProgram copy fx anchor := by
 unfold program fixedProgram
 calc
  NNH_RecordedCharge.recorder copy (base fx H) fx.indexError fx.reservation
   (DGP_HostDigest.hashvInst H) fx.a (fx.Q0+fx.Q1) =
   NNH_RecordedCharge.recorder copy (base fx H) fx.indexError fx.reservation
    (fun _ => .ok digest0) fx.a (fx.Q0+fx.Q1) :=
    NNH_DigestSyntaxTransport.o1 copy _ _ _ H digest0 fx.a _
  _ = NNH_RecordedCharge.recorder copy (base fx anchor) fx.indexError fx.reservation
    (fun _ => .ok digest0) fx.a (fx.Q0+fx.Q1) :=
    NNQ_HostDigest.o2 (NNH8_Exec.seed (env fx H)) copy fx.indexError fx.reservation
     (env fx H) (env fx anchor) (fun _ => .ok digest0) fx.a _ rfl rfl rfl
  _ = _ := (NNH_DigestSyntaxTransport.o1 copy _ _ _ anchor digest0 fx.a _).symm

#print axioms AspisR1.NNH8_RecorderFixed.fixed
end AspisR1.NNH8_RecorderFixed
namespace AspisR1.NNH8_HostCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open NOC_Run5bCtx NNH8_RecorderFixed
open FS FS2

/-- SAME event for every oracle outcome; no realized-pair condition. -/
theorem event_fixed
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (fx : Fixed) (H anchor : Bytes → State) :
 NNH8_Exec.ERec copy fx H ↔
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
 NNH_RecordedCharge.bound copy (NNH8_RecorderFixed.base fx anchor) fx.indexError fx.reservation
  (DGP_HostDigest.hashvInst anchor) fx.a (fx.Q0+fx.Q1)

#print axioms AspisR1.NNH8_HostCharge.event_fixed
#print axioms AspisR1.NNH8_HostCharge.bound
end AspisR1.NNH8_HostCharge
namespace AspisR1.NNH8_FullSpace
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NOC_Run5bCtx
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem realizes (fx : Fixed) (wOf : (Bytes → State) → World W Tx) (H : Bytes → State) :
 (NNH8_Exec.recSig L copy std).Realizes
  (RSL.TASB.ctxB (NNH8_Exec.exec L copy std) fx (wOf H) H) :=
 RSL.TASB.realizes_by_construction (NNH8_Exec.exec L copy std) fx (wOf H) H

theorem same_event (fx : Fixed) (wOf : (Bytes → State) → World W Tx)
 (H anchor : Bytes → State) :
 (NNH8_Exec.recSig L copy std).EventRec
  (RSL.TASB.ctxB (NNH8_Exec.exec L copy std) fx (wOf H) H) ↔
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
  (eval H (NNH8_RecorderFixed.fixedProgram copy fx anchor)) :=
 NNH8_HostCharge.event_fixed copy fx H anchor
#print axioms AspisR1.NNH8_FullSpace.realizes
#print axioms AspisR1.NNH8_FullSpace.same_event
end AspisR1.NNH8_FullSpace
end
