import PV_DIAG2_Termination
/-! log 0.4.33 macro outer gates. The deployed log feature list is empty,
so release STATIC_MAX_LEVEL is Trace. Level evaluation, atomic filter load,
argument evaluation, dispatch and cleanup have complete effect interfaces.
No global claim that a dependency cannot change the filter/logger is made. -/
set_option autoImplicit false
namespace PV_DIAG2
inductive LogLevel where
 | error | warn | info | debug | trace
 deriving DecidableEq, Repr

def levelNumber : LogLevel → Nat
 | .error => 1 | .warn => 2 | .info => 3 | .debug => 4 | .trace => 5

def logMacro (staticMax : Nat) (level : Execution LogLevel) (loadMax : Execution Nat)
    (dispatch : LogLevel → Execution Unit) : Execution Unit :=
 bind level (fun l => if levelNumber l ≤ staticMax then
  bind loadMax (fun m => if levelNumber l ≤ m then dispatch l else pureExecution ())
  else pureExecution ())


theorem log_static_guard_silent (staticMax : Nat) (l : LogLevel) (prior : List Effect) (loadMax : Execution Nat) (dispatch : LogLevel → Execution Unit)
 (h : ¬ levelNumber l ≤ staticMax) :
 logMacro staticMax ⟨prior,.value l⟩ loadMax dispatch = ⟨prior,.value ()⟩ := by simp [logMacro,bind,prepend,pureExecution,h]
#print axioms log_static_guard_silent

theorem log_runtime_off_skips_arguments (l : LogLevel) (prior loaded : List Effect) (dispatch : LogLevel → Execution Unit) :
 logMacro 5 ⟨prior,.value l⟩ ⟨loaded,.value 0⟩ dispatch = ⟨prior++loaded,.value ()⟩ := by cases l <;> simp [logMacro,levelNumber,bind,prepend,pureExecution]
#print axioms log_runtime_off_skips_arguments

theorem log_enabled_dispatch (staticMax maximum : Nat) (l : LogLevel) (prior loaded : List Effect) (dispatch : LogLevel → Execution Unit)
 (hs : levelNumber l ≤ staticMax) (hm : levelNumber l ≤ maximum) :
 logMacro staticMax ⟨prior,.value l⟩ ⟨loaded,.value maximum⟩ dispatch = prepend (prior++loaded) (dispatch l) := by simp [logMacro,hs,hm,bind,prepend,List.append_assoc]
#print axioms log_enabled_dispatch

theorem log_level_panic (staticMax : Nat) (prior : List Effect) (msg : String) (pcs : List Nat) (loadMax : Execution Nat) (dispatch : LogLevel → Execution Unit) :
 logMacro staticMax ⟨prior,.panic msg pcs⟩ loadMax dispatch = ⟨prior,.panic msg pcs⟩ := rfl
#print axioms log_level_panic

theorem log_level_oom (staticMax : Nat) (prior : List Effect) (size : Nat) (pcs : List Nat) (loadMax : Execution Nat) (dispatch : LogLevel → Execution Unit) :
 logMacro staticMax ⟨prior,.oom size pcs⟩ loadMax dispatch = ⟨prior,.oom size pcs⟩ := rfl
#print axioms log_level_oom

theorem log_load_panic (staticMax : Nat) (l : LogLevel) (prior loaded : List Effect) (msg : String) (pcs : List Nat) (dispatch : LogLevel → Execution Unit)
 (hs : levelNumber l ≤ staticMax) :
 logMacro staticMax ⟨prior,.value l⟩ ⟨loaded,.panic msg pcs⟩ dispatch = ⟨prior++loaded,.panic msg pcs⟩ := by simp [logMacro,hs,bind,prepend]
#print axioms log_load_panic

theorem log_dispatch_panic (staticMax maximum : Nat) (l : LogLevel) (prior loaded emitted : List Effect) (msg : String) (pcs : List Nat) (dispatch : LogLevel → Execution Unit)
 (hs : levelNumber l ≤ staticMax) (hm : levelNumber l ≤ maximum) (hd : dispatch l = ⟨emitted,.panic msg pcs⟩) :
 logMacro staticMax ⟨prior,.value l⟩ ⟨loaded,.value maximum⟩ dispatch = ⟨prior++loaded++emitted,.panic msg pcs⟩ := by simp [logMacro,hs,hm,hd,bind,prepend,List.append_assoc]
#print axioms log_dispatch_panic

theorem log_dispatch_oom (staticMax maximum : Nat) (l : LogLevel) (prior loaded emitted : List Effect) (size : Nat) (pcs : List Nat) (dispatch : LogLevel → Execution Unit)
 (hs : levelNumber l ≤ staticMax) (hm : levelNumber l ≤ maximum) (hd : dispatch l = ⟨emitted,.oom size pcs⟩) :
 logMacro staticMax ⟨prior,.value l⟩ ⟨loaded,.value maximum⟩ dispatch = ⟨prior++loaded++emitted,.oom size pcs⟩ := by simp [logMacro,hs,hm,hd,bind,prepend,List.append_assoc]
#print axioms log_dispatch_oom
end PV_DIAG2
