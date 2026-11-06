import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep10
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 10=ok (values p 10) := by
 exact p.amount_sub
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 10) :
 left pub o st 10=left pub o (values p) 10 ∧
 right pub st 10=right pub (values p) 10 := by
 constructor
 · rfl
 · exact ready 9 (by decide)
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 10) : call pub o s st 10=ok (values p 10) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep10
end
