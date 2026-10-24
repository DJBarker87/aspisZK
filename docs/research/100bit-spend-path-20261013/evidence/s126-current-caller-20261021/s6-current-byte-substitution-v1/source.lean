import S6CurrentPublicAdmissionV1
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open VTop_Stages AspisR1.VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7
namespace AspisS6CurrentByteSubstitution
open AspisS6CurrentFirstInstallation

/-- The actual source byte entry's two-pass source/model substitution with
its S6 admission premise discharged. The original library trust and all
thirteen body joins remain; the model dictionary is not identified with frozen2. -/
theorem substitute (adapter : _root_.AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (ops : VTop_Stages.Ops) (trusted : Port1_Library.TrustedStd ops)
    (source model : Implementation) (bodies : Port1_DriverSubstitution.BodyJoins source model)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (submission : Port1_StoredCarrier.Submission) (H : Bytes → State)
    (accepted : (eval H (Port1_ByteDriver.rust (install adapter vops)
      (Port1_Library.implementation ops source) D hash submission)).2=true) :
    eval H (Port1_ByteDriver.rust (install adapter vops)
      (Port1_Library.implementation ops source) D hash submission) =
    eval H (Port1_ByteDriver.rust (install adapter vops)
      (Port1_Library.implementation (Port1_Library.std ops) model) D hash submission) :=
  Port1_ByteDriver.substitute (install adapter vops)
    (AspisS6CurrentPublicAdmission.publicAdmission adapter vops) ops trusted source model bodies
    D hash submission H accepted

#print axioms substitute
end AspisS6CurrentByteSubstitution
