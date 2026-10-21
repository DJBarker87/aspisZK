import Aeneas
set_option autoImplicit false
namespace AspisR1.MultiproofConeVecLaws
open Aeneas Aeneas.Std Result

theorem empty_bytes : (alloc.vec.Vec.new U8).val = [] := rfl

theorem clone_bytes (s : Slice U8) :
    Slice.clone core.clone.CloneU8.clone s = ok s := by
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone:=core.clone.CloneU8.clone) (s:=s) (by intros; rfl))
  simpa only [←hv] using ho

theorem to_vec_bytes (s : Slice U8) :
    alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok s := clone_bytes s

theorem extend_success (v out : alloc.vec.Vec U8) (s : Slice U8)
    (h : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok out) :
    out.val = v.val ++ s.val := by
  have hc := clone_bytes s
  unfold alloc.vec.Vec.extend_from_slice at h
  split at h
  · split at h
    · rename_i cloned he
      have hs : cloned = s := Result.ok.inj (he.symm.trans hc)
      subst cloned
      have ho := Result.ok.inj h
      subst out
      rfl
    · rename_i e he
      rw [he] at hc
      cases hc
    · rename_i he
      rw [he] at hc
      cases hc
  · cases h

theorem extend_total (v : alloc.vec.Vec U8) (s : Slice U8)
    (bound : v.val.length + s.val.length ≤ Usize.max) :
    ∃ out, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 v s = ok out ∧
      out.val = v.val ++ s.val := by
  refine ⟨⟨v.val++s.val,by simpa only [List.length_append] using bound⟩,?_,rfl⟩
  have hc := clone_bytes s
  unfold alloc.vec.Vec.extend_from_slice
  simp only [show v.length + s.length ≤ Usize.max from bound, dif_pos]
  split
  · rename_i cloned he
    have hs : cloned = s := Result.ok.inj (he.symm.trans hc)
    subst cloned
    rfl
  · rename_i e he
    rw [he] at hc
    cases hc
  · rename_i he
    rw [he] at hc
    cases hc

theorem push_success {α : Type} (v out : alloc.vec.Vec α) (x : α)
    (h : alloc.vec.Vec.push v x = ok out) : out.val = v.val ++ [x] := by
  unfold alloc.vec.Vec.push at h
  dsimp only at h
  split at h
  · have he := Result.ok.inj h
    subst out
    exact List.concat_eq_append
  · cases h

#print axioms empty_bytes
#print axioms clone_bytes
#print axioms to_vec_bytes
#print axioms extend_success
#print axioms extend_total
#print axioms push_success
end AspisR1.MultiproofConeVecLaws
