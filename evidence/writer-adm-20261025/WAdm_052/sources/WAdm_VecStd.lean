import WAdm_Fissioned.Funs
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_VecStd

theorem clone (s : Slice U8) : Slice.clone core.clone.CloneU8.clone s = ok s := by
  obtain ⟨out,call,same⟩ := spec_imp_exists
    (@Slice.clone_spec U8 core.clone.CloneU8.clone s (by intro x hx; rfl))
  rw [← same] at call
  exact call

theorem extend (out : alloc.vec.Vec U8) (s : Slice U8)
    (bound : out.val.length + s.val.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s =
      ok ⟨out.val ++ s.val,by simpa only [List.length_append] using bound⟩ := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos bound,clone]

#print axioms clone
#print axioms extend
end AspisR1.WAdm_VecStd
end
