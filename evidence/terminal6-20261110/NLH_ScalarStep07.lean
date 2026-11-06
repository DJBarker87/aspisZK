import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep07
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 7=ok (values p 7) := by
 exact p.product_calls 2
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 7) :
 left pub o st 7=left pub o (values p) 7 ∧
 right pub st 7=right pub (values p) 7 := by
 constructor
 · exact ready 6 (by decide)
 · exact ready 1 (by decide)
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 7) : call pub o s st 7=ok (values p 7) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep07
end
