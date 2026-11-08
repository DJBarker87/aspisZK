import NNH_Run5bHostCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Run5bFullSpace
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_Run5bCtx
variable {W Tx : Type} (L : Library W (Nat → Record))
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (std : S2W_TrustedStd.TrustedStd copy)

theorem realizes (fx : Fixed) (wOf : (Bytes → State) → World W Tx) (H : Bytes → State) :
 (NNH_Run5bExec.recSig L copy std).Realizes
  (RSL.TASB.ctxB (NNH_Run5bExec.exec L copy std) fx (wOf H) H) :=
 RSL.TASB.realizes_by_construction (NNH_Run5bExec.exec L copy std) fx (wOf H) H

theorem same_event (fx : Fixed) (wOf : (Bytes → State) → World W Tx)
 (H anchor : Bytes → State) :
 (NNH_Run5bExec.recSig L copy std).EventRec
  (RSL.TASB.ctxB (NNH_Run5bExec.exec L copy std) fx (wOf H) H) ↔
 BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (fx.Q0+fx.Q1+2965)
  (eval H (NNH_Run5bRecorderFixed.fixedProgram copy fx anchor)) :=
 NNH_Run5bHostCharge.event_fixed copy fx H anchor
#print axioms realizes
#print axioms same_event
end AspisR1.NNH_Run5bFullSpace
end
