import NKI_ValueTraceFactor
import NKI_ArrayFrame
import RPv_FIy_ValueShifts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueFrames
open Aeneas Aeneas.Std Result FIq_Native
open NKI_ValuePrefix (Openings Selectors)
open NKI_ValueTrace (Locals)
theorem source (o : Openings) (s : Selectors) (l : Locals) (calls : NKI_ValueTrace.Clauses o s l) :
 l.i=1024#u32 ∧ l.i1=1048576#u32 ∧
 (∀ j : Fin 33,NJB_ArrayCarrier.cell l.range6 j=if j.val=30 then l.q12 else if j.val=31 then l.q13 else if j.val=32 then l.q14 else NJB_ArrayCarrier.cell l.range3 j) := by
 have c_i : 1#u32 <<< 10#i32=ok l.i := calls.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_i1 : 1#u32 <<< 20#i32=ok l.i1 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_range4 : Array.update l.range3 30#usize l.q12=ok l.range4 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_range5 : Array.update l.range4 31#usize l.q13=ok l.range5 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
 have c_range6 : Array.update l.range5 32#usize l.q14=ok l.range6 := calls.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
 refine ⟨UScalar.eq_of_val_eq (FIy_ValueShifts.ten _ c_i),UScalar.eq_of_val_eq (FIy_ValueShifts.twenty _ c_i1),?_⟩
 intro j
 rw [NKI_ArrayFrame.update _ _ _ _ c_range6 j,NKI_ArrayFrame.update _ _ _ _ c_range5 j,NKI_ArrayFrame.update _ _ _ _ c_range4 j]
 by_cases h30 : j.val=30 <;> by_cases h31 : j.val=31 <;> by_cases h32 : j.val=32 <;> simp [h30,h31,h32,eq_comm]
#print axioms source
end AspisR1.NKI_ValueFrames
end
