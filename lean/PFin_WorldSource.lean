import PFin_WorldRuns
import F3U_SourceInputs
import F3U_AsSliceBytes
import F3Q_SliceIdentity
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_WorldSource
open Aeneas Aeneas.Std Result MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier F3V_RunEvidence

theorem program {F C : Type} (c : Configuration F C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (s : Submission)
    (H : Bytes → State) (e : Evidence c B s H)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (accepted : (eval H (F3T_Installed.source c hashv (input c s))).2=true) :
    F3T_Installed.source c hashv (input c s)=
      DrvC_PairProgram.source c hashv e.semantic e.pub e.proof := by
  obtain ⟨pub,proof,semantic,hpub,hproof,decoded,source,yes⟩ := F3U_SourceInputs.accepted c hashv s H accepted
  have pubEq : pub=e.pub := F3Q_SliceIdentity.slice _ _ ((F3U_AsSliceBytes.inverse _ _ hpub).trans e.pubBytes.symm)
  have proofEq : proof=e.proof := F3Q_SliceIdentity.slice _ _ ((F3U_AsSliceBytes.inverse _ _ hproof).trans e.proofBytes.symm)
  subst pub
  subst proof
  have semEq : semantic=e.semantic := Option.some.inj (Result.ok.inj (decoded.symm.trans e.decoded))
  subst semantic
  exact source

#print axioms program
end AspisR1.PFin_WorldSource
end
