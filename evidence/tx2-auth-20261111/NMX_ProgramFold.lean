import NMX_Program
set_option autoImplicit false
noncomputable section
namespace NMX_ProgramFold
open Aeneas Aeneas.Std NMX_OwnedPackets NMX_Program
/-- Source-ordered assume/guarantee fold. A concrete parent instantiation must
supply each entered child's full packet at its SAME command and current world.
This generic law is not a native row root and contains no success-only join. -/
theorem congruence {W E A : Type} (native model : Handler W E)
 (children : ∀ {B : Type} (cmd : Command B) (w : W), native cmd w = model cmd w)
 (term : Program A) (before : W) : eval native term before = eval model term before := by
 induction term generalizing before with
 | ret a => rfl
 | reject error => rfl
 | stop cause => rfl
 | @step B cmd next ih =>
   simp only [eval, children cmd before]
   cases h : model cmd before with
   | stopped es cause => rfl
   | returned reply post es =>
     cases reply with
     | Err error => rfl
     | Ok value => exact congrArg (prepend es) (ih value post)

/-- All outcomes, post-world fields and events are compared by congruence;
there is no projection to returned success. -/
theorem returned {W E A : Type} (native model : Handler W E)
 (children : ∀ {B : Type} (cmd : Command B) (w : W), native cmd w = model cmd w)
 (term : Program A) (before post : W) (reply : core.result.Result A AdapterRw.solana_program_error.ProgramError)
 (events : List E) (result : eval model term before = .returned reply post events) :
 eval native term before = .returned reply post events := by
 rw [congruence native model children term before,result]

theorem stopped {W E A : Type} (native model : Handler W E)
 (children : ∀ {B : Type} (cmd : Command B) (w : W), native cmd w = model cmd w)
 (term : Program A) (before : W) (events : List E) (cause : Stop)
 (result : eval model term before = .stopped events cause) :
 eval native term before = .stopped events cause := by
 rw [congruence native model children term before,result]
#print axioms congruence
#print axioms returned
#print axioms stopped
end NMX_ProgramFold
end
