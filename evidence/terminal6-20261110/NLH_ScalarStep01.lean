import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarStep01
open Aeneas Aeneas.Std Result FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet amount)
theorem actual {pub o s before} (p : Packet pub o s before) :
 call pub o s (values p) 1=ok (values p 1) := by
 exact p.asset_sub
theorem operands {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 1) :
 left pub o st 1=left pub o (values p) 1 ∧
 right pub st 1=right pub (values p) 1 := by
 constructor
 · rfl
 · exact ready 0 (by decide)
theorem call_ready {pub o s before} (p : Packet pub o s before) (st : State)
 (ready : Ready p st 1) : call pub o s st 1=ok (values p 1) := by
 have args := operands p st ready
 unfold call
 rw [args.1,args.2]
 exact actual p
#print axioms actual
#print axioms operands
#print axioms call_ready
end AspisR1.NLH_ScalarStep01
end
