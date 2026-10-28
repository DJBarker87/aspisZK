import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Truncate
open PV_OWN_Heap PV_OWN_View PV_OWN_Operations
/-- The post-truncate view retains the same allocation and initialized bytes.
Dropping removed values is a separate, type-specific operation. -/
theorem view {T : Type} (k : Codec T) (m : Memory) (v : Vector T) (n : Nat)
 (h:VecView k m v) : VecView k m (truncate n v) := by
 obtain ⟨c,owned,size,align,bound,repr⟩:=h
 refine ⟨c,owned,size,align,?_,?_⟩
 · simp only [truncate,List.length_take]; omega
 · intro i x hi
   apply repr i x
   have hh:=List.getElem?_take v.values n i
   simp only [truncate] at hi
   rw [hh] at hi
   split at hi
   · exact hi
   · cases hi
#print axioms view
end R1Z.PV_OWN_Truncate
