import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep11
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 11=ok (values p 11) := by
 exact p.product_calls 3
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 11) :
 left pub o st 11=left pub o (values p) 11 ∧
 right pub st 11=right pub (values p) 11 := by
 constructor
 · exact ready 8 (by decide)
 · exact ready 10 (by decide)
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 11) : call pub o s st 11=ok (values p 11) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep11
end
