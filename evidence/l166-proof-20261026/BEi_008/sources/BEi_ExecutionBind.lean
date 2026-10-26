import BEi_ExecutionUnique
import BEf_Bind
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEi_ExecutionBind
open Aeneas Aeneas.Std Result SdkC_Source BEi_Execution

/-- A continuation consumes the SAME intermediate state and chronological log. -/
theorem success {S A B : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (k : A → Code B) (state middle after : S)
    (before prefixLog log : Log) (a : A) (value : Result B)
    (first : Executes call code state before (.ok a) middle prefixLog)
    (second : Executes call (k a) middle prefixLog value after log) :
    Executes call (code >>= k) state before value after log := by
  apply (BEi_ExecutionUnique.iff_run call _ _ _ _ _ _).mpr
  rw [BEf_Bind.run,BEi_Execution.sound call code state middle before prefixLog (.ok a) first]
  exact BEi_Execution.sound call (k a) middle after prefixLog log value second

/-- An outer error cannot execute the later branch or erase its own prefix. -/
theorem failure {S A B : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (k : A → Code B) (state after : S)
    (before log : Log) (error : Error)
    (first : Executes call code state before (.fail error) after log) :
    Executes call (code >>= k) state before (.fail error) after log := by
  apply (BEi_ExecutionUnique.iff_run call _ _ _ _ _ _).mpr
  rw [BEf_Bind.run,BEi_Execution.sound call code state after before log (.fail error) first]
  rfl

theorem divergence {S A B : Type} (call : Parts → S → Result Digest × S)
    (code : Code A) (k : A → Code B) (state after : S)
    (before log : Log)
    (first : Executes call code state before .div after log) :
    Executes call (code >>= k) state before .div after log := by
  apply (BEi_ExecutionUnique.iff_run call _ _ _ _ _ _).mpr
  rw [BEf_Bind.run,BEi_Execution.sound call code state after before log .div first]
  rfl

#print axioms success
#print axioms failure
#print axioms divergence
end AspisR1.BEi_ExecutionBind
end
