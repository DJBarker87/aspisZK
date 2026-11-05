import NIY_FirstRawCut
set_option autoImplicit false
noncomputable section
namespace NIY_RawTransport
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1

/-- A raw read transports both the value and the very same reader into the continuation. -/
theorem raw {A B : Type} (f : A → B) (n : Usize) (r : Fresh.R)
 (left : Array U8 n → Fresh.R → Result A)
 (right : Array U8 n → Cohort.R → Result B)
 (h : ∀ x out,outer f (left x (unReader out))=right x out) :
 outer f (do let (x,out) ← NIL_FreshOps.raw n r;left x out)=
 (do let (x,out) ← CheckpointBytes3Reader.raw n (reader r);right x out) := by
 unfold NIL_FreshOps.raw
 apply NIL_PortBind.source
 rintro ⟨x,out⟩
 exact h x out

/-- First3 raw32 continuation transport. The continuation premise is explicit and remains open. -/
theorem first3 {A B : Type} (f : A → B) (bytes : Slice U8)
 (left : Array U8 32#usize → Array U8 32#usize → Array U8 32#usize → Fresh.R → Result A)
 (right : Array U8 32#usize → Array U8 32#usize → Array U8 32#usize → Cohort.R → Result B)
 (h : ∀ state a3 a4 out,outer f (left state a3 a4 (unReader out))=right state a3 a4 out) :
 outer f (do
   let (state,r) ← NIL_FreshOps.raw 32#usize {bytes, «at» := 80#usize}
   let (a3,r1) ← NIL_FreshOps.raw 32#usize r
   let (a4,r2) ← NIL_FreshOps.raw 32#usize r1
   left state a3 a4 r2)=
 (do
   let (state,r) ← CheckpointBytes3Reader.raw 32#usize {bytes, «at» := 80#usize}
   let (a3,r1) ← CheckpointBytes3Reader.raw 32#usize r
   let (a4,r2) ← CheckpointBytes3Reader.raw 32#usize r1
   right state a3 a4 r2) := by
 apply raw
 intro state r
 apply raw
 intro a3 r1
 apply raw
 intro a4 r2
 exact h state a3 a4 r2
#print axioms raw
#print axioms first3
end NIY_RawTransport
