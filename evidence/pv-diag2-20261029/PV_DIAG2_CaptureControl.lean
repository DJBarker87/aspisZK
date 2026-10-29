import PV_DIAG2_BacktraceFlags
import PV_DIAG2_Termination
set_option autoImplicit false
namespace PV_DIAG2

/-- Scope continuations retain owned String/VarError drop glue, comparison
and all normal/unwind cleanup effects. They must be supplied from native
execution, and are never defaulted to identity. -/
def readBacktraceEnv (library fallback : Execution EnvRead)
    (closeLibrary closeFallback : EnvRead → Execution Bool → Execution Bool) : Execution Bool :=
 bind library (fun value => closeLibrary value (match value with
  | .value s => pureExecution (s != "0")
  | _ => bind fallback (fun value => closeFallback value (pureExecution (envFlag value)))))

def enabledExecution (load : Execution Nat) (library fallback : Execution EnvRead)
    (closeLibrary closeFallback : EnvRead → Execution Bool → Execution Bool)
    (store : Nat → Execution Unit) : Execution Bool :=
 bind load (fun value => match value with
  | 0 => bind (readBacktraceEnv library fallback closeLibrary closeFallback) (fun b =>
    bind (store (cacheCode b)) (fun _ => pureExecution b))
  | 1 => pureExecution false
  | _+2 => pureExecution true)

inductive BacktraceValue where
 | disabled | unsupported | captured : List Nat → BacktraceValue
 deriving Repr

def captureExecution (enabled : Execution Bool) (create : Execution BacktraceValue) :
    Execution BacktraceValue :=
 bind enabled (fun flag => if flag then create else pureExecution .disabled)

def forceCaptureExecution (create : Execution BacktraceValue) := create


theorem env_unicode_skips_fallback (prior : List Effect) (s : String) (fallback : Execution EnvRead)
 (cl cb : EnvRead → Execution Bool → Execution Bool) :
 readBacktraceEnv ⟨prior,.value (.value s)⟩ fallback cl cb = prepend prior (cl (.value s) (pureExecution (s != "0"))) := rfl
#print axioms env_unicode_skips_fallback

theorem env_absent_runs_fallback (prior : List Effect) (fallback : Execution EnvRead)
 (cl cb : EnvRead → Execution Bool → Execution Bool) :
 readBacktraceEnv ⟨prior,.value .absent⟩ fallback cl cb = prepend prior (cl .absent (bind fallback (fun value => cb value (pureExecution (envFlag value))))) := rfl
#print axioms env_absent_runs_fallback

theorem env_nonunicode_runs_fallback (prior : List Effect) (fallback : Execution EnvRead)
 (cl cb : EnvRead → Execution Bool → Execution Bool) :
 readBacktraceEnv ⟨prior,.value .nonUnicode⟩ fallback cl cb = prepend prior (cl .nonUnicode (bind fallback (fun value => cb value (pureExecution (envFlag value))))) := rfl
#print axioms env_nonunicode_runs_fallback

theorem env_panic_retained (prior : List Effect) (msg : String) (pcs : List Nat) (fallback : Execution EnvRead)
 (cl cb : EnvRead → Execution Bool → Execution Bool) :
 readBacktraceEnv ⟨prior,.panic msg pcs⟩ fallback cl cb = ⟨prior,.panic msg pcs⟩ := rfl
#print axioms env_panic_retained

theorem fallback_oom_scope_retained (prior tail : List Effect) (size : Nat) (pcs : List Nat)
 (cl cb : EnvRead → Execution Bool → Execution Bool) :
 readBacktraceEnv ⟨prior,.value .nonUnicode⟩ ⟨tail,.oom size pcs⟩ cl cb =
 prepend prior (cl .nonUnicode ⟨tail,.oom size pcs⟩) := rfl
#print axioms fallback_oom_scope_retained

theorem cached_off_no_env (prior : List Effect) (lib back : Execution EnvRead)
 (cl cb : EnvRead → Execution Bool → Execution Bool) (store : Nat → Execution Unit) :
 enabledExecution ⟨prior,.value 1⟩ lib back cl cb store = ⟨prior,.value false⟩ := by simp [enabledExecution,bind,prepend,pureExecution]
#print axioms cached_off_no_env

theorem cached_on_no_env (prior : List Effect) (n : Nat) (lib back : Execution EnvRead)
 (cl cb : EnvRead → Execution Bool → Execution Bool) (store : Nat → Execution Unit) :
 enabledExecution ⟨prior,.value (n+2)⟩ lib back cl cb store = ⟨prior,.value true⟩ := by simp [enabledExecution,bind,prepend,pureExecution]
#print axioms cached_on_no_env

theorem disabled_no_create (prior : List Effect) (create : Execution BacktraceValue) :
 captureExecution ⟨prior,.value false⟩ create = ⟨prior,.value .disabled⟩ := by simp [captureExecution,bind,prepend,pureExecution]
#print axioms disabled_no_create

theorem enabled_keeps_create (prior : List Effect) (create : Execution BacktraceValue) :
 captureExecution ⟨prior,.value true⟩ create = prepend prior create := rfl
#print axioms enabled_keeps_create

theorem force_capture_bypasses_env (create : Execution BacktraceValue) : forceCaptureExecution create = create := rfl
#print axioms force_capture_bypasses_env
end PV_DIAG2
