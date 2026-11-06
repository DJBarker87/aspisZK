import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep05
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 5=ok (values p 5) := by
 exact p.product_calls 1
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 5) :
 left pub o st 5=left pub o (values p) 5 ∧
 right pub st 5=right pub (values p) 5 := by
 constructor
 · exact ready 4 (by decide)
 · exact ready 1 (by decide)
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 5) : call pub o s st 5=ok (values p 5) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep05
end
