import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_BackendStore55
open Aeneas Aeneas.Std Result

theorem index_mut {T : Type} (values : alloc.vec.Vec T) (i : Usize)
    (bound : i.val<values.length) :
    ∃ value back,alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) values i=ok (value,back) ∧
      back=alloc.vec.Vec.set values i := by
  obtain ⟨⟨value,back⟩,run,post⟩ := Aeneas.Std.WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec values i bound)
  refine ⟨value,back,?_,post.2⟩
  rw [alloc.vec.Vec.index_mut_slice_index]
  exact run

theorem length {T : Type} (values : alloc.vec.Vec T) (i : Usize) (value : T) :
    (alloc.vec.Vec.set values i value).length=values.length := alloc.vec.Vec.set_length ..
#print axioms index_mut
#print axioms length
end R1Z.PV_RunJoin_BackendStore55
