import NKI_InitialInvocation
import NKI_ArrayFrame
import RPv_FIx_ScheduleIndices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_InitialFrames
open Aeneas Aeneas.Std Result FIq_Native
open NKI_InitialPrefix (Public Openings Selectors)
open NKI_InitialInvocation (Locals)
theorem source (p : Public) (o : Openings) (s : Selectors) (l : Locals)
 (calls : NKI_InitialInvocation.Clauses p o s l) :
 ∀ j : Fin 16,NJB_ArrayCarrier.cell l.initial2 j=
 if j.val=8 then l.q24 else if j.val=9 then l.q27 else NJB_ArrayCarrier.cell l.initial j := by
 have c_i : poseidon2.RATE+1#usize=ok l.i := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_initial1 : Array.update l.initial poseidon2.RATE l.q24=ok l.initial1 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_initial2 : Array.update l.initial1 l.i l.q27=ok l.initial2 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have vi:=FIx_ScheduleIndices.rate_plus_one l.i c_i
 intro j
 rw [NKI_ArrayFrame.update _ _ _ _ c_initial2 j,vi,NKI_ArrayFrame.update _ _ _ _ c_initial1 j]
 by_cases h8 : j.val=8 <;> by_cases h9 : j.val=9 <;> simp [poseidon2.RATE,h8,h9,eq_comm]
#print axioms source
end AspisR1.NKI_InitialFrames
end
