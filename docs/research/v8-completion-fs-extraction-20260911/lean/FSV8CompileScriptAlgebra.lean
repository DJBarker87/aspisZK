import FSV8V7OracleMachineBridge
import AspisFormal.K1.V7Tag73SharedOracleVerifierRunner

/-!
# Compiler algebra for bounded transcript scripts

These structural laws show that compilation erases only the static call-budget
padding and preserves sequential composition.  They are independent of the V8
protocol and do not use interpreter-run extensionality.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 200000

namespace AspisV8Completion.FSV8CompileScriptAlgebra

open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSV8V7OracleMachineBridge
open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73SharedOracleVerifierRunner

abbrev Bytes := List UInt8
abbrev Block := FSBoundedTranscript.Block

theorem compileScript_promote {A : Type} {n : Nat}
    (script : Script Bytes Block A n) :
    compileScript (promote script) = compileScript script := by
  induction script with
  | done value => rfl
  | abort => rfl
  | ask input next ih =>
      simp only [promote, compileScript]
      congr 1
      funext output
      exact ih output

theorem compileScript_pad {A : Type} {n : Nat}
    (script : Script Bytes Block A n) (extra : Nat) :
    compileScript (pad script extra) = compileScript script := by
  induction extra with
  | zero => rfl
  | succ extra ih =>
      rw [pad, compileScript_promote, ih]

theorem compileScript_bind {A B : Type} {m n : Nat}
    (script : Script Bytes Block A n)
    (next : A → Script Bytes Block B m) :
    compileScript (bind script next) =
      bindOracleMachine (compileScript script)
        (fun value => compileScript (next value)) := by
  induction script with
  | done value =>
      rw [FSTranscriptScript.bind, compileScript, bindOracleMachine]
      exact compileScript_pad (next value) _
  | abort => rfl
  | ask input continuation ih =>
      change
        OracleMachine.query input (fun output =>
          compileScript (FSTranscriptScript.bind (continuation output) next)) =
        OracleMachine.query input (fun output =>
          bindOracleMachine (compileScript (continuation output))
            (fun value => compileScript (next value)))
      apply congrArg (OracleMachine.query input)
      funext output
      exact ih output

theorem bindOracleMachine_assoc {A B C : Type}
    (script : OracleMachine A) (next : A → OracleMachine B)
    (last : B → OracleMachine C) :
    bindOracleMachine (bindOracleMachine script next) last =
      bindOracleMachine script
        (fun value => bindOracleMachine (next value) last) := by
  induction script with
  | pure value => rfl
  | abort reason => rfl
  | query input continuation ih =>
      simp only [bindOracleMachine]
      congr 1
      funext output
      exact ih output

#print axioms compileScript_promote
#print axioms compileScript_pad
#print axioms compileScript_bind
#print axioms bindOracleMachine_assoc

end AspisV8Completion.FSV8CompileScriptAlgebra
