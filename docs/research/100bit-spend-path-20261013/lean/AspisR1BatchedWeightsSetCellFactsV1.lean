import AspisR1BatchedWeightsPushBodyValueStepV2
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1BatchedWeightsSetCellFactsV1

theorem array_set_cell {α : Type} {a : Array α 4#usize} (i : Usize)
    (hi : i.val < 4) (x : α) :
    (a.set i x).val[i.val]'(by simpa [a.property, List.length_set] using hi) = x := by
  have hset : i.val < (a.val.set i.val x).length := by
    simpa [List.length_set] using (show i.val < a.val.length by simpa [a.property] using hi)
  change (a.val.set i.val x)[i.val]'hset = x
  exact List.getElem_set_self hset

theorem array_set_frame {α : Type} {a : Array α 4#usize}
    (i k : Usize) (hi : i.val < 4) (hk : k.val < 4)
    (hne : i.val ≠ k.val) (x : α) :
    (a.set i x).val[k.val]'(by simpa [a.property, List.length_set] using hk) =
      a.val[k.val]'(by simpa [a.property] using hk) := by
  have hkSet : k.val < (a.val.set i.val x).length := by
    simpa [List.length_set] using (show k.val < a.val.length by simpa [a.property] using hk)
  change (a.val.set i.val x)[k.val]'hkSet = a.val[k.val]'(by simpa [a.property] using hk)
  exact List.getElem_set_ne hne hkSet

theorem vec_set_selected {α : Type} (v : alloc.vec.Vec α) (i : Usize)
    (hi : i.val < v.length) (x : α) :
    (alloc.vec.Vec.set v i x).val[i.val]'(by simpa [List.length_set] using hi) = x := by
  have hset : i.val < (v.val.set i.val x).length := by
    simpa [List.length_set] using hi
  change (v.val.set i.val x)[i.val]'hset = x
  exact List.getElem_set_self hset

theorem vec_set_frame {α : Type} (v : alloc.vec.Vec α) (i k : Usize)
    (hi : i.val < v.length) (hk : k.val < v.length)
    (hne : i.val ≠ k.val) (x : α) :
    (alloc.vec.Vec.set v i x).val[k.val]'(by simpa [List.length_set] using hk) =
      v.val[k.val]'(by simpa using hk) := by
  have hkSet : k.val < (v.val.set i.val x).length := by
    simpa [List.length_set] using hk
  change (v.val.set i.val x)[k.val]'hkSet = v.val[k.val]'(by simpa using hk)
  exact List.getElem_set_ne hne hkSet

#print axioms array_set_cell
#print axioms array_set_frame
#print axioms vec_set_selected
#print axioms vec_set_frame
end AspisR1BatchedWeightsSetCellFactsV1
