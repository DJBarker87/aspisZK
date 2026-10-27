import ART_WrapperAccepted
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_PrefixCoupling
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.SqueezeOracleBridge

/-- The failed call itself remains in the actual attempted prefix. No ideal
suffix after failure is counted as actual work. This holds in every world. -/
theorem source {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) (before : Log) :
    ∃ tail, (eval H (SdkC_Oracle.program code)).1 =
      (eval H (ART_PartialProgram.program hashv code before)).1 ++ tail := by
  induction code generalizing before with
  | done a => exact ⟨[],rfl⟩
  | step r k ih =>
    cases r with
    | ok a => exact ih a before
    | fail e => exact ⟨[],rfl⟩
    | div => exact ⟨[],rfl⟩
  | read parts k ih =>
    cases answer : hashv parts with
    | ok digest =>
      obtain ⟨tail,log⟩ := ih (encodeState (H (flatten parts)))
        (before ++ [⟨parts,ok (encodeState (H (flatten parts)))⟩])
      refine ⟨tail,?_⟩
      simpa only [SdkC_Oracle.program,ART_PartialProgram.program,eval,answer,List.cons_append] using
        congrArg (List.cons (flatten parts,H (flatten parts))) log
    | fail error =>
      exact ⟨(eval H (SdkC_Oracle.program (k (encodeState (H (flatten parts)))))).1,by simp only [SdkC_Oracle.program,ART_PartialProgram.program,eval,answer,List.singleton_append]⟩
    | div =>
      exact ⟨(eval H (SdkC_Oracle.program (k (encodeState (H (flatten parts)))))).1,by simp only [SdkC_Oracle.program,ART_PartialProgram.program,eval,answer,List.singleton_append]⟩

theorem cost {A : Type} (hashv : Parts → Result Digest) (H : Bytes → State)
    (code : Code A) :
    (eval H (ART_PartialAccount.wrapper hashv code)).1.length ≤
      (eval H (SdkC_Oracle.program code)).1.length := by
  obtain ⟨tail,log⟩ := source hashv H code []
  simp only [ART_PartialAccount.wrapper,AspisV8R19.OracleProgramOps.eval_bind,eval,List.append_nil]
  rw [log,List.length_append]
  omega

#print axioms source
#print axioms cost
end AspisR1.ART_PrefixCoupling
end
