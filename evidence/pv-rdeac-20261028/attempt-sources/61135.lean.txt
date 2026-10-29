import R1Z.PV_RDEAC_AppendSimulation
open Aeneas Aeneas.Std Result
namespace R1Z.PV_RDEAC_VectorProjection

theorem extend (v : alloc.vec.Vec U8) (s : Slice U8)
    (bound : v.val.length+s.val.length≤Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s=
      ok ⟨v.val++s.val,by rw [List.length_append];exact bound⟩ := by
  unfold alloc.vec.Vec.extend_from_slice
  simp only [alloc.vec.Vec.length,Slice.length,dif_pos bound]
  split <;> rename_i h
  all_goals have hh:=PV_RDEAC_AppendSimulation.clone_bytes s
  all_goals rw [hh] at h
  all_goals cases h
  rfl

#print alloc.vec.Vec.push
#print Slice.len
#print axioms extend
end R1Z.PV_RDEAC_VectorProjection
