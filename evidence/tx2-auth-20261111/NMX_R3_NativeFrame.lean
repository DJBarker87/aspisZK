import NMX_R3_LaneAllocation
set_option autoImplicit false
namespace NMX_R3_NativeFrame
open Aeneas Aeneas.Std
local instance {m : Usize} : Inhabited (Array U32 m) := ⟨Array.repeat m 0#u32⟩

/-- Join native assignment and iterator frame contracts. Both are universally
quantified over their observed coordinates; this proves equality of the WHOLE
updated frontier, including untouched cells, without reducing a concrete loop. -/
theorem write_unique {n m : Usize} (before after : Array (Array U32 m) n)
 (i : Usize) (value : Array U32 m) (index : i.val < n.val)
 (selected : ∀ c, c < m.val →
  NCV_ArrayFrame.coord (NCV_ArrayFrame.coord after i.val) c = NCV_ArrayFrame.coord value c)
 (frame : ∀ j, j < n.val → j ≠ i.val → ∀ c, c < m.val →
  NCV_ArrayFrame.coord (NCV_ArrayFrame.coord after j) c =
  NCV_ArrayFrame.coord (NCV_ArrayFrame.coord before j) c) :
 after = before.set i value := by
 apply NCV_ArrayFrame.whole
 intro j _ hj
 apply NCV_ArrayFrame.whole
 intro c _ hc
 rw [NCV_ArrayFrame.set_at before i value j index hj]
 by_cases hit : i.val = j
 · subst j
   simp only [↓reduceIte]
   exact selected c hc
 · simp only [hit, ↓reduceIte]
   exact frame j hj (Ne.symm hit) c hc

/-- Whole returned payload from native observations: scalar fields retain their
representations, with no canonicality restriction imposed on incoming cells. -/
theorem lane (a b : NCV_Reference.Lane)
 (bump : a.bump=b.bump) (master : a.master=b.master) (lane_id : a.lane_id=b.lane_id)
 (next : a.next_leaf_index=b.next_leaf_index) (root : a.root=b.root)
 (frontier : a.frontier=b.frontier) : a=b := by
 cases a
 cases b
 simp_all
#print axioms write_unique
#print axioms lane
end NMX_R3_NativeFrame
