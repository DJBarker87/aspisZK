import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep02
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 2=ok (values p 2) := by
 exact p.row_calls 0
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 2) :
 left pub o st 2=left pub o (values p) 2 ∧
 right pub st 2=right pub (values p) 2 := by
 constructor
 · rfl
 · rfl
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 2) : call pub o s st 2=ok (values p 2) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep02
end
