import Aeneas
set_option autoImplicit false
namespace R1Z.ProverRw21VecAppend
open Aeneas Aeneas.Std Result

theorem clone_bytes (s : Slice U8) : Slice.clone core.clone.CloneU8.clone s=ok s := by
  have ⟨result,hr,heq⟩ := WP.spec_imp_exists (Slice.clone_spec
    (s := s) (clone := core.clone.CloneU8.clone) (by intros; rfl))
  rw [← heq] at hr
  exact hr

def append (out : alloc.vec.Vec U8) (s : Slice U8)
    (bound : out.length+s.length≤Usize.max) : alloc.vec.Vec U8 :=
  ⟨out.val++s.val,by simpa only [List.length_append] using bound⟩

theorem exact_append (out : alloc.vec.Vec U8) (s : Slice U8)
    (bound : out.length+s.length≤Usize.max) :
    alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s=ok (append out s bound) := by
  unfold alloc.vec.Vec.extend_from_slice
  rw [dif_pos bound]
  have hc := clone_bytes s
  split
  · rename_i result hr
    have eq : result=s := Result.ok.inj (hr.symm.trans hc)
    subst result
    rfl
  · rename_i error hr
    rw [hc] at hr
    cases hr
  · rename_i hr
    rw [hc] at hr
    cases hr

#print axioms clone_bytes
#print axioms append
#print axioms exact_append
end R1Z.ProverRw21VecAppend
