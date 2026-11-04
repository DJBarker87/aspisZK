import PV_STX_Composition
set_option autoImplicit false
namespace PV_STX_CallbackEffects
open Aeneas Aeneas.Std PV_STX_Code PV_STX_Machine
variable {Op : Type → Type 1}

/-- Port of evhB CallbackEffects, with reached primitive requests in place
of arbitrary completed computations. Argument destruction precedes capture. -/
def construct {E C F : Type} (dropArgument : E → Op Unit)
    (dropCapture : C → Op Unit) (value : F) (closure : C) (error : E) : Code Op F := do
  let _ ← Code.call (dropArgument error)
  let _ ← Code.call (dropCapture closure)
  pure value

def mapErr {T E C F : Type} (dropArgument : E → Op Unit)
    (dropCapture : C → Op Unit) (value : F)
    (result : Except E T) (closure : C) : Code Op (Except F T) :=
  match result with
  | .ok x => do
    let _ ← Code.call (dropCapture closure)
    pure (.ok x)
  | .error e => do
    let out ← construct dropArgument dropCapture value closure e
    pure (.error out)

/-- Ruling (y) substitution for two primitive child replies. The premises
are local call answers at the actual pre/post-worlds, never a helper trace.
Pending is separately retained by Machine.pending_call_retains. -/
theorem construct_returned {E C F W Ev : Type} (handler : Handler Op W Ev)
    (da : E → Op Unit) (dc : C → Op Unit) (value : F) (closure : C) (error : E)
    (w : W) (r : Result Unit)
    (ha : (handler (da error) w).answer = .returned (.ok ()))
    (hc : (handler (dc closure) (handler (da error) w).world).answer = .returned r) :
    run handler 5 (construct da dc value closure error) w =
      ⟨.returned (match r with | .ok _ => .ok value | .fail e => .fail e | .div => .div),
       (handler (dc closure) (handler (da error) w).world).world,
       (handler (da error) w).events ++
         (handler (dc closure) (handler (da error) w).world).events⟩ := by
  cases r <;>
    simp only [construct,Bind.bind,Pure.pure,run,advance,start,step,resumed,continueWith,ha,hc,
      List.nil_append,List.append_nil]

theorem argument_fault {E C F W Ev : Type} (handler : Handler Op W Ev)
    (da : E → Op Unit) (dc : C → Op Unit) (value : F) (closure : C) (error : E)
    (w : W) (fault : Fault) (h : (handler (da error) w).answer = .fault fault) :
    run handler 5 (construct da dc value closure error) w =
      ⟨.fault fault,(handler (da error) w).world,(handler (da error) w).events⟩ := by
  simp only [construct,Bind.bind,Pure.pure,run,advance,start,step,h,List.nil_append]

#print axioms construct_returned
#print axioms argument_fault
end PV_STX_CallbackEffects
