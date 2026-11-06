import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep03
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 3=ok (values p 3) := by
 exact p.product_calls 0
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 3) :
 left pub o st 3=left pub o (values p) 3 ∧
 right pub st 3=right pub (values p) 3 := by
 constructor
 · exact ready 2 (by decide)
 · exact ready 1 (by decide)
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 3) : call pub o s st 3=ok (values p 3) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep03
end
