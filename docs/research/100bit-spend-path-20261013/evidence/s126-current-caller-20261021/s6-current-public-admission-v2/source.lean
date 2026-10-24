import S6CurrentFirstInstallationV1
import Port1_ByteDriver
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
open VTop_Stages AspisR1.VTop_OracleCode
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1 OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7
namespace AspisS6CurrentPublicAdmission
open AspisS6CurrentFirstInstallation

theorem decoded_length (ops : _root_.AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (pub : Slice U8) (semantic : Port1_Driver.Semantic)
    (accepted : Port1_Driver.decodeSemantic (install ops vops) pub=ok (some semantic)) :
    pub.val.length=1880 := by
  unfold Port1_Driver.decodeSemantic at accepted
  cases run : (install ops vops).op47 pub with
  | fail error => simp only [run,bind_tc_fail] at accepted; cases accepted
  | div => simp only [run,bind_tc_div] at accepted; cases accepted
  | ok reply =>
    cases reply with
    | Err error => simp only [run,bind_tc_ok] at accepted; cases accepted
    | Ok statement =>
      obtain ⟨encoded,_,same⟩ := AspisS6CurrentCodecInstallation.accepted_inverse pub statement run
      have length : encoded.val.length=1880 := by simpa using encoded.property
      rw [same] at length
      exact length

/-- The actual decoder/validator's successful selection derives admission;
no independent public-length or encoder-success hypothesis remains. -/
theorem publicAdmission (ops : _root_.AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops) :
    Port1_ByteDriver.PublicAdmission (install ops vops) := by
  intro pub semantic accepted
  rw [decoded_length ops vops pub semantic accepted]
  change 75+1880≤131072
  omega

/-- Original physical byte entry and canonical carrier, with S6 admission
supplied by the concrete codec. No extra physical acceptance gate is added. -/
theorem accepted_transport (ops : _root_.AdapterRw.Ops) (vops : AspisR1CurrentCaller.Ops)
    (impl : Implementation) {Hash : Type} (D : aspis_core.digest.Digest32 Hash)
    (hash : Hash) (submission : Port1_StoredCarrier.Submission) (H : Bytes → State)
    (accepted : (eval H (Port1_ByteDriver.rust (install ops vops) impl D hash submission)).2=true) :
    Port1_ByteDriver.rust (install ops vops) impl D hash submission =
      Port1_Driver.rust (install ops vops) impl D hash (Port1_StoredCarrier.input submission) :=
  Port1_ByteDriver.accepted_transport (install ops vops) (publicAdmission ops vops)
    impl D hash submission H accepted

#print axioms decoded_length
#print axioms publicAdmission
#print axioms accepted_transport
end AspisS6CurrentPublicAdmission
