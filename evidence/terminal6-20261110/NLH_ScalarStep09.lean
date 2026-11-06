import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep09
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 9=ok (values p 9) := by
 exact FIw_ScalarArithmetic.lift_run (amount pub)
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 9) :
 left pub o st 9=left pub o (values p) 9 ∧
 right pub st 9=right pub (values p) 9 := by
 constructor
 · rfl
 · rfl
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 9) : call pub o s st 9=ok (values p 9) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep09
end
