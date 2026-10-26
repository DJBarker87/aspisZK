import F3T_TwoPass
import DrvC_SourceEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Installed
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_TwoPass

def source {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) : Verifier := fun i =>
  match Port1_Driver.asSlice i.physical.bytes,Port1_Driver.asSlice i.stored with
  | some pub,some proof =>
    match Port1_Driver.decodeSemantic (DrvC_Installation.sdk c) pub with
    | .ok (some semantic) => DrvC_PairProgram.source c hashv semantic pub proof
    | _ => .done false
  | _,_ => .done false

theorem physical {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (i j : F3_Model.Input)
    (pub : i.physical.bytes=j.physical.bytes) (stored : i.stored=j.stored) :
    source c hashv i=source c hashv j := by
  simp only [source,pub,stored]

theorem annotation {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
    AnnotationInvariant (source c hashv) := by
  intro w i
  exact physical c hashv _ _ rfl rfl

theorem old_source {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (i : F3_Model.Input) (j : OraclePortStoredExperimentC4.Input)
    (pub : i.physical.bytes=j.statement.pubBytes) (stored : i.stored=j.stored) :
    source c hashv i=DrvC_SourceEntry.source c hashv j := by
  simp only [source,DrvC_SourceEntry.source,pub,stored]

theorem installed {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (i : F3_Model.Input) (j : OraclePortStoredExperimentC4.Input)
    (pub : i.physical.bytes=j.statement.pubBytes) (stored : i.stored=j.stored) :
    source (DrvC_FirstConstants.configuration c) hashv i=
      DrvC_Implementation.driver (DrvC_FirstConstants.configuration c) j := by
  rw [old_source _ hashv i j pub stored,DrvC_SourceEntry.same_program c hashv]

#print axioms physical
#print axioms annotation
#print axioms old_source
#print axioms installed
end AspisR1.F3T_Installed
end
