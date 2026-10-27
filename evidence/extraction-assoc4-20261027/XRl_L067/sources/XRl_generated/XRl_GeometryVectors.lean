import XRk_VectorLength
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_GeometryVectors
/-- Local namespace avoids the incompatible generated discriminant owners
imported transitively by Port4C_GeometryStd (retained failure L063). -/
theorem clone (s : Slice aspis_core.field.M31) :
    Slice.clone aspis_core.field.M31.Insts.CoreCloneClone.clone s=ok s := by
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists
    (Slice.clone_spec (clone:=aspis_core.field.M31.Insts.CoreCloneClone.clone) (s:=s) (by intros; rfl))
  simpa only [←hv] using ho

theorem extend (flat out : alloc.vec.Vec aspis_core.field.M31)
    (s : Slice aspis_core.field.M31)
    (run : alloc.vec.Vec.extend_from_slice aspis_core.field.M31.Insts.CoreCloneClone flat s=ok out) :
    out.val=flat.val++s.val := by
  have hc := clone s
  unfold alloc.vec.Vec.extend_from_slice at run
  split at run
  · split at run
    · rename_i cloned he
      have hs : cloned=s := Result.ok.inj (he.symm.trans hc)
      subst cloned
      cases Result.ok.inj run
      rfl
    · rename_i e he
      rw [he] at hc
      cases hc
    · rename_i he
      rw [he] at hc
      cases hc
  · cases run
#print axioms clone
#print axioms extend
end XRl_GeometryVectors
