import NGY_SourceStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGY_Result
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NGU_LPm_RawPort
open AspisR1CurrentPreparedClaim

def mapped (reply : core.result.Result Unit Unit) : core.result.Result Unit verifier.Error :=
 match reply with
 | .Ok _ => .Ok ()
 | .Err _ => .Err .Parse

/-- The complete Rust record's full Result, control, state and ordered log. -/
def G (lane : Nat) (before after : Native) (value : NE) (scalar : NQ)
 (reply : core.result.Result Unit Unit) :=
 (mapped reply, NGY_Oracle.G lane before after value scalar reply)

def reference (lane : Nat) (before after : Native) (value : NE) (scalar : NQ)
 (reply : core.result.Result Unit Unit) :=
 (mapped reply, NGY_Oracle.reference lane before after value scalar reply)

theorem association (lane : Nat) (before after : Native) (value : NE) (scalar : NQ)
 (reply : core.result.Result Unit Unit) :
 reference lane before after value scalar reply=G lane before after value scalar reply := by
 rw [reference,G,NGY_Oracle.reference_eq_G]

theorem error (lane : Nat) (before after : Native) (value : NE) (scalar : NQ) :
 reference lane before after value scalar (.Err ())=
  (core.result.Result.Err verifier.Error.Parse,
   NGY_Oracle.Control.parse lane,after,[NGY_Oracle.Entry.mk value scalar before after (.Err ())]) := rfl

theorem success (lane : Nat) (before after : Native) (value : NE) (scalar : NQ) :
 reference lane before after value scalar (.Ok ())=
  (core.result.Result.Ok (),
   NGY_Oracle.Control.advance (lane+1),after,[NGY_Oracle.Entry.mk value scalar before after (.Ok ())]) := rfl

#print axioms association
#print axioms error
#print axioms success
end AspisR1.NGY_Result
end
