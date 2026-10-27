import RPz8_ARU_Header
import RPz8_SCH_Oracle
import RPz7_GExq_RetainedReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_ReaderHeader
open Aeneas Aeneas.Std Result VTop_Stages
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.SqueezeOracleBridge

theorem ideal (reserved : Bool) (H : Bytes → State) (ck proof pub : Slice U8)
    (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : (eval H (SdkC_Oracle.program
      (GExq_RetainedReader.code reserved ck proof pub .S2))).2 = ok (.Ok (p,a))) :
    CPhy_Header.decode (MultiproofConeCanonical.bytesOf ck.val) =
      some (H (MultiproofConeCanonical.bytesOf proof.val),H (MultiproofConeCanonical.bytesOf pub.val)) := by
  let D : VTop_Stages.aspis_core.digest.Digest32 Unit :=
    { coremarkerCopyInst := (SdkC_Source.dictionary (SCH_Oracle.ideal H)).coremarkerCopyInst
      digest := fun _ parts => SCH_Oracle.ideal H parts }
  have source := (SCH_Oracle.evaluation H (GExq_RetainedReader.code reserved ck proof pub .S2) []).1.trans success
  rw [SdkC_Source.erasure,GExq_RetainedReader.source reserved (SCH_Oracle.ideal H) D () (fun _ => rfl),
    Port4A_ReaderInstall.reference_eq] at source
  have resume := Port3_CheckpointInstall.reader_success reserved D ck proof pub .S2 () p a source
  apply ARU_Header.reader reserved (VTop_Checkpoint.digest D) () H ck proof pub p a _ resume
  intro parts digest issued returned
  have same : encodeState (H (flatten parts)) = digest := Result.ok.inj returned
  rw [←same]
  exact state_roundtrip _

#print axioms ideal
end AspisR1.ARU_ReaderHeader
end
