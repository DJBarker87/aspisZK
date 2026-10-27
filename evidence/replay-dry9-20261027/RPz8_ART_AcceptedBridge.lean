import RPz8_ART_WrapperExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_AcceptedBridge
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.SqueezeOracleBridge

/-- In EVERY world, acceptance of the status-preserving interpreter excludes
all failed-syscall branches. No compatibility or global native P1 is required. -/
theorem source {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (before : Log) (value : A)
    (accepted : (eval H (ART_PartialProgram.program hashv code before)).2.1 = ok value) :
    eval H (SdkC_Oracle.program code) =
      ((eval H (ART_PartialProgram.program hashv code before)).1,ok value) := by
  induction code generalizing before with
  | done a =>
    have same : a = value := Result.ok.inj accepted
    cases same
    rfl
  | step r k ih =>
    cases r with
    | ok a => exact ih a before accepted
    | fail e => cases accepted
    | div => cases accepted
  | read parts k ih =>
    cases answer : hashv parts with
    | fail e => simp only [ART_PartialProgram.program,eval,answer] at accepted; cases accepted
    | div => simp only [ART_PartialProgram.program,eval,answer] at accepted; cases accepted
    | ok digest =>
      have next := ih (encodeState (H (flatten parts)))
        (before ++ [⟨parts,ok (encodeState (H (flatten parts)))⟩])
        (by simpa only [ART_PartialProgram.program,eval,answer] using accepted)
      simpa only [SdkC_Oracle.program,ART_PartialProgram.program,eval,answer] using
        congrArg (fun v => ((flatten parts,H (flatten parts))::v.1,v.2)) next

#print axioms source
end AspisR1.ART_AcceptedBridge
end
