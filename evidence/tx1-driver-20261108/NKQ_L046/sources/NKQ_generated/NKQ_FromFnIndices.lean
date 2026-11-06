import NKQ_ArrayWindows
set_option autoImplicit false
namespace AspisR1.NKQ_FromFnIndices
open Aeneas Aeneas.Std Result

theorem bound (n i : Usize) (member : i∈OraclePortStdBuilder.indices n) : i.val<n.val := by
 unfold OraclePortStdBuilder.indices at member
 obtain ⟨j,rfl⟩:=List.mem_ofFn.mp member
 scalar_tac

theorem length (n : Usize) : (OraclePortStdBuilder.indices n).length=n.val := by
 simp only [OraclePortStdBuilder.indices,List.length_ofFn]

/-- One source state-preserving callback per actual index, then symbolic
induction through the original library loop. No concrete recurrence reduced. -/
theorem total {T C : Type} (n : Usize) (f : core.ops.function.FnMut C Usize T)
 (g : Usize → T) (c : C)
 (step : ∀ i,i.val<n.val → f.call_mut c i=ok (g i,c)) :
 OraclePortStdBuilder.fromFn n f c=
 ok (⟨(OraclePortStdBuilder.indices n).map g,by simp [length]⟩ : Array T n) := by
 have loop:=NKQ_ArrayWindows.fromFnLoop_bounded f g c (OraclePortStdBuilder.indices n)
   (fun i member=>step i (bound n i member))
 simp [OraclePortStdBuilder.fromFn,loop,length]
#print axioms bound
#print axioms length
#print axioms total
end AspisR1.NKQ_FromFnIndices
