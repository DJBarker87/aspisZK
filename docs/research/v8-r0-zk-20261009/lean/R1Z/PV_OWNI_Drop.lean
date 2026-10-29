import R1Z.PV_OWNI_Transfer
set_option autoImplicit false
namespace R1Z.PV_OWNI_Drop
open PV_OWN_Heap PV_OWN_Operations PV_W_Threading
/-- (usize,QM31) has no Drop implementation. IntoIter's remaining-slice drop
has no element events; RawVec deallocation uses allocation capacity, not len. -/
theorem backing {S X E : Type}
 (primitive : Nat → Request → S → Outcome E Unit × S)
 (w : State S X) (t : Token) (c : Cell) (positive:0<c.size) :
 dropVecPod primitive t c w=
 ⟨(primitive t.address ⟨c.size,c.alignment⟩ w.allocator).1,
  {w with allocator:=(primitive t.address ⟨c.size,c.alignment⟩ w.allocator).2,
   memory:=retire t c w.memory},[(w,.deallocate t.address c.size c.alignment)]⟩ := by
 rw [dropVecPod,if_neg (by omega)]
 rfl

theorem retired {S X E : Type}
 (primitive : Nat → Request → S → Outcome E Unit × S)
 (w : State S X) (t : Token) (c : Cell) (positive:0<c.size) :
 (dropVecPod primitive t c w).world.memory.heap t.address=some {c with live:=false} := by
 rw [backing primitive w t c positive]
 exact put_same _ _ _

theorem pod_no_effect {S X E : Type} (w : State S X) :
 (dropPod (E:=E) w).calls=[] ∧ (dropPod (E:=E) w).world=w := ⟨rfl,rfl⟩
#print axioms backing
#print axioms retired
#print axioms pod_no_effect
end R1Z.PV_OWNI_Drop
