import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep04
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 4=ok (values p 4) := by
 exact p.row_calls 1
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 4) :
 left pub o st 4=left pub o (values p) 4 ∧
 right pub st 4=right pub (values p) 4 := by
 constructor
 · rfl
 · rfl
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 4) : call pub o s st 4=ok (values p 4) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep04
end
