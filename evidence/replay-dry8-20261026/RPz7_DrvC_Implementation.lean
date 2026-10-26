import RPz7_DrvC_Dictionary
import RPz7_GExp_RetainedReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_Implementation
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_Carriers Tx1Q_Carriers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Freeze the literal library constants and release observer implementation.
All body slots remain those in the supplied installed configuration. -/
def release {F C : Type} (c : Configuration F C) : Configuration F C :=
  { c with stageBase := Port1_Library.install (Port1_Library.std c.stageBase) }

/-- Full typed preparation tree, including its ordered digest calls. -/
def prepare {F C H : Type} (c : Configuration F C)
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : Port1_Driver.Semantic) (proof : Slice U8) (hash : H)
    (scratch : Array S.E 29#usize) :=
  DrvC_Program.mapCode DrvC_Dictionary.prepareReply
    (SdkD_PrepareLower.lower (SdkD_PrepareSource.code (current c) c.boundaries c.std
      (AspisS6CurrentFirstInstallation.toDigest D)
      (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash (arr unE scratch)))

/-- Dependent call interpreter constructed from the installed source bodies.
No body-program, compatibility or acceptance argument is supplied. -/
def implementation {F C : Type} (c : Configuration F C) : VTop_OracleCode.Implementation :=
  fun call => match call with
  | .op5 D proof p root which hash =>
      SdkC_Oracle.program (SdkC_BatchSource.mapCode Op5T_Install.stageError
        (SdkC_BatchSource.code (VTop_Checkpoint.digest D) hash proof p.queries p.roots root which))
  | .op7 D pub proof hash obs scratch =>
      match obs with
      | none => SdkC_Oracle.program (prepare c D pub proof hash scratch)
      | some observer => .done ((DrvC_Dictionary.ops c).op7 D pub proof hash (some observer) scratch)
  | .op8 _ p a proof pub _ =>
      SdkC_Oracle.program (GExp_FirstCode.writerCode (unPrepared p) (unAccumulator a) proof pub)
  | .op18 _ ck proof pub v _ =>
      SdkC_Oracle.program (GExp_RetainedReader.code c.reserved ck proof pub v)
  | op => .done (VTop_Trace.invoke (DrvC_Dictionary.ops c) op)

def driver {F C : Type} (c : Configuration F C) : OraclePortRuntimeBindingC7.Verifier :=
  Port1_Driver.rust (sdk c) (implementation c) (digest c) ()

theorem physical {F C : Type} (c : Configuration F C) :
    Port1_StoredCarrier.Physical (driver c) :=
  Port1_StoredCarrier.driver_physical (sdk c) (implementation c) (digest c) ()

theorem finish_call {F C : Type} (c : Configuration F C)
    (v : VTop_Stages.verifier.View) (p : S.P) (a : S.A) :
    implementation c (.op19 v p a none) =
      .done (Port4D_FinishInstall.finish c.finish v p a none) := rfl

theorem resume_call {F C H : Type} (c : Configuration F C)
    (D : VTop_Stages.aspis_core.digest.Digest32 H) (hash : H)
    (ck proof pub : Slice U8) (v : VTop_Stages.transport.Variant) :
    implementation c (.op18 D ck proof pub v hash) =
      SdkC_Oracle.program (GExp_RetainedReader.code c.reserved ck proof pub v) := rfl

#print axioms physical
#print axioms finish_call
#print axioms resume_call
#print implementation
end AspisR1.DrvC_Implementation
end
