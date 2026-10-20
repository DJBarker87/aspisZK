import GeometryInputsExplicitQuery
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1GeometryInputs.Proof
open alloc.vec

theorem slice_clone_identity (s : Slice M31) :
    Slice.clone M31.Insts.CoreCloneClone.clone s = .ok s := by
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone:=M31.Insts.CoreCloneClone.clone) (s:=s) (by intros; rfl))
  simpa only [←hv] using ho

theorem extend_success (v out : Vec M31) (s : Slice M31)
    (h : Vec.extend_from_slice M31.Insts.CoreCloneClone v s = .ok out) :
    out.val = v.val ++ s.val := by
  unfold Vec.extend_from_slice at h
  split at h
  · split at h
    · rename_i s1 hc
      have hs : s1 = s := Result.ok.inj (hc.symm.trans (slice_clone_identity s))
      subst s1
      have he := Result.ok.inj h
      subst out
      rfl
    · cases h
    · cases h
  · cases h

theorem push_success (v out : Vec M31) (x : M31)
    (h : Vec.push v x = .ok out) : out.val = v.val ++ [x] := by
  unfold Vec.push at h
  dsimp only at h
  split at h
  · have he := Result.ok.inj h
    subst out
    exact List.concat_eq_append
  · cases h

#print axioms slice_clone_identity
#print axioms extend_success
#print axioms push_success
end AspisR1GeometryInputs.Proof
