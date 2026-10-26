import BEf_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_Execution
open Aeneas Aeneas.Std Result SdkC_Source

/-- Small-step cut semantics for the existing source effect language. The
state after a failed syscall is retained. This relation is not a physical
runtime admission: associating an actual runtime cut is a separate obligation. -/
inductive Executes {S A : Type} (call : Parts → S → Result Digest × S) :
    Code A → S → Log → Result A → S → Log → Prop where
  | done (a : A) (state : S) (before : Log) :
      Executes call (.done a) state before (.ok a) state before
  | stepOk {B : Type} (a : B) (k : B → Code A) (state after : S)
      (before log : Log) (value : Result A)
      (next : Executes call (k a) state before value after log) :
      Executes call (.step (.ok a) k) state before value after log
  | stepFail {B : Type} (error : Error) (k : B → Code A) (state : S) (before : Log) :
      Executes call (.step (.fail error) k) state before (.fail error) state before
  | stepDiv {B : Type} (k : B → Code A) (state : S) (before : Log) :
      Executes call (.step .div k) state before .div state before
  | readOk (parts : Parts) (k : Digest → Code A) (state middle after : S)
      (before log : Log) (digest : Digest) (value : Result A)
      (called : call parts state = (.ok digest,middle))
      (next : Executes call (k digest) middle (before ++ [⟨parts,.ok digest⟩]) value after log) :
      Executes call (.read parts k) state before value after log
  | readFail (parts : Parts) (k : Digest → Code A) (state after : S)
      (before : Log) (error : Error) (called : call parts state = (.fail error,after)) :
      Executes call (.read parts k) state before (.fail error) after (before ++ [⟨parts,.fail error⟩])
  | readDiv (parts : Parts) (k : Digest → Code A) (state after : S)
      (before : Log) (called : call parts state = (.div,after)) :
      Executes call (.read parts k) state before .div after (before ++ [⟨parts,.div⟩])

/-- Operational cuts uniquely determine the complete source interpreter result. -/
theorem sound {S A : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (state after : S) (before log : Log) (value : Result A)
    (run : Executes call code state before value after log) :
    BEf_Carrier.run call code state before = (value,after,log) := by
  induction run with
  | done => rfl
  | stepOk a k state after before log value next ih => exact ih
  | stepFail => rfl
  | stepDiv => rfl
  | readOk parts k state middle after before log digest value called next ih =>
    simpa only [BEf_Carrier.run,called] using ih
  | readFail parts k state after before error called => simp only [BEf_Carrier.run,called]
  | readDiv parts k state after before called => simp only [BEf_Carrier.run,called]

#print axioms sound
end AspisR1.BEi_Execution
end
