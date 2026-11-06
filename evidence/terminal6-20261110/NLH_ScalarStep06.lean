import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep06
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 6=ok (values p 6) := by
 exact p.row_calls 2
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 6) :
 left pub o st 6=left pub o (values p) 6 ∧
 right pub st 6=right pub (values p) 6 := by
 constructor
 · rfl
 · rfl
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 6) : call pub o s st 6=ok (values p 6) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep06
end
