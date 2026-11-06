import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep08
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 8=ok (values p 8) := by
 exact p.row_calls 3
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 8) :
 left pub o st 8=left pub o (values p) 8 ∧
 right pub st 8=right pub (values p) 8 := by
 constructor
 · rfl
 · rfl
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 8) : call pub o s st 8=ok (values p 8) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep08
end
