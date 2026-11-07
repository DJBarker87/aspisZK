import NLZ_Subwindow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLZ_Split087
open Aeneas Aeneas.Std AspisR1.NLZ_Resources
def Disjoint (a b : Window) : Prop :=
 a.allocation≠b.allocation ∨ a.offset+a.length≤b.offset ∨ b.offset+b.length≤a.offset
/-- The logical allocation is shared; two view tokens do not create two owners.
No native allocation success follows from this geometry law. -/
theorem split (h : Heap) (logical : Window) (bytes : List U8)
 (view : View h logical bytes) (extent : logical.length=14759) :
 View h (subwindow logical 0 13831) (bytes.take 13831) ∧
 View h (subwindow logical 13831 928) ((bytes.drop 13831).take 928) ∧
 Disjoint (subwindow logical 0 13831) (subwindow logical 13831 928) := by
 have left := subview h logical bytes 0 13831 view (by omega)
 have right := subview h logical bytes 13831 928 view (by omega)
 refine ⟨?_,right,?_⟩
 · simpa only [List.drop_zero] using left
 · exact Or.inr (Or.inl (by simp [subwindow]))
#print axioms split
#print split
end AspisR1.NLZ_Split087
end
