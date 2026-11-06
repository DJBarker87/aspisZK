import NLB_State
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)
/-- The (bb)/(bc) rejection observation; the native full Err is retained
separately. This is not a claim that Rust returns an Aeneas panic. -/
def reject {A : Type} : R A → Result A
 | .ok (.Ok a) => .ok a
 | .ok (.Err _) => .fail .panic
 | .fail e => .fail e
 | .div => .div

/-- Exact native Err may correspond to cohort fail, or the full Results may
already agree. This includes duplicate Err exits that the cohort preserves. -/
inductive ReplyRel : R Unit → R Unit → Prop where
 | same (reply : R Unit) : ReplyRel reply reply
 | rejected (error : verifier.Error) : ReplyRel (.ok (.Err error)) (.fail .panic)

def question {A : Type} (reply : R Unit) (next : Unit → R A) : R A := do
 let r ← reply
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue value => next value
 | .Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     A (core.convert.FromSame verifier.Error) residual

theorem bind_congr {A B : Type} (m : Result A) (native source : A → R B)
 (tail : ∀ a,reject (native a)=reject (source a)) :
 reject (Bind.bind (m:=Result) m native)=reject (Bind.bind (m:=Result) m source) := by
 cases m with
 | ok value => exact tail value
 | fail error => rfl
 | div => rfl

/-- The native Err continuation and cohort abort have identical rejection;
no successful child or caller assumption is needed. -/
theorem question_rel {A : Type} (native source : R Unit)
 (nativeTail sourceTail : Unit → R A) (child : ReplyRel native source)
 (tail : ∀ u,reject (nativeTail u)=reject (sourceTail u)) :
 reject (question native nativeTail)=reject (question source sourceTail) := by
 cases child with
 | rejected error => rfl
 | same =>
   cases native with
   | fail error => rfl
   | div => rfl
   | ok r =>
     cases r with
     | Err error => rfl
     | Ok u => exact tail u

/-- Native Err and cohort fail cannot be substituted as equal full Results. -/
theorem error_not_equal (error : verifier.Error) :
 (ok (.Err error) : R Unit)≠fail .panic := by intro impossible;cases impossible
#print axioms bind_congr
#print axioms question_rel
#print axioms error_not_equal
end NLB_ErrorTransport
