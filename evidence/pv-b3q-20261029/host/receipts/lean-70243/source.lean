import PV_B3Q_Iterator4
namespace PV_B3Q_Iterator4
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
def Aligned (state : Enumerated) : Prop := state.count = state.iter.index
/-- The actual constructor establishes the count/pointer relation; it is not an
assumption about an arbitrary caller-created Enumerate state. -/
theorem constructor_alignment (region : Nat) (cells : Four14) :
    ∃ state, (do let iter ← source_new region cells; source_enumerate_new iter) = .ok state ∧
      Aligned state := by
 refine ⟨⟨⟨region,0#usize,by scalar_tac⟩,0#usize⟩,rfl,rfl⟩
/-- Every returned loan points to the enumerated group in the same region.
The terminal None branch preserves both counters. -/
theorem aligned_next (state : Enumerated) (aligned : Aligned state) :
    ∃ item advanced, source_enumerate_next state = .ok (item,advanced) ∧
      Aligned advanced ∧
      (∀ group slot, item = some (group,slot) →
        group = slot.index ∧ slot.region = advanced.iter.region ∧ slot.index.val < 4) := by
 by_cases finish : state.iter.index = 4#usize
 · refine ⟨none,{iter := state.iter,count := state.count},?_,aligned,?_⟩
   · simp only [source_enumerate_next,source_next,finish,dif_pos,bind_tc_ok]
   · intro group slot impossible
     cases impossible
 · have small : state.iter.index.val < 4 := by
     have bound := state.iter.valid
     have different : state.iter.index.val ≠ 4 := by
       intro h
       apply finish
       apply UScalar.eq_of_val_eq
       exact h
     omega
   let iter := advance state.iter small
   let result : Enumerated := ⟨iter,Usize.wrapping_add state.count 1#usize⟩
   refine ⟨some (state.count,⟨state.iter.region,state.iter.index⟩),result,?_,?_,?_⟩
   · simp only [source_enumerate_next,source_next,finish,dif_neg,bind_tc_ok]
     rfl
   · change Usize.wrapping_add state.count 1#usize = Usize.wrapping_add state.iter.index 1#usize
     rw [aligned]
   · intro group slot same
     have pair := Option.some.inj same
     have hg : group = state.count := (congrArg Prod.fst pair).symm
     have hs : slot = ⟨state.iter.region,state.iter.index⟩ := (congrArg Prod.snd pair).symm
     subst group
     subst slot
     exact ⟨aligned,rfl,small⟩
#print axioms constructor_alignment
#print axioms aligned_next
end PV_B3Q_Iterator4
