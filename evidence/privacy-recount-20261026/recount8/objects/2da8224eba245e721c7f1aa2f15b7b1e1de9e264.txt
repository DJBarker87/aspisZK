import R1Z.PV_RunJoin_ByteAppend38
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CloneBytes43
open Aeneas Aeneas.Std Result

theorem complete (s : Slice U8) :
    ∃ next, alloc.slice.Slice.to_vec core.clone.CloneU8 s=.ok next ∧ next.val=s.val := by
  have hclone : Slice.clone core.clone.CloneU8.clone s=.ok s := by
    obtain ⟨s',heq,hs⟩ := WP.spec_imp_exists
      (Slice.clone_spec (s := s) (clone := core.clone.CloneU8.clone) (by intro x _;rfl))
    simpa only [←hs] using heq
  change Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) s=.ok s at hclone
  refine ⟨⟨s.val,s.property⟩,?_,rfl⟩
  simp only [alloc.slice.Slice.to_vec]
  rw [hclone]
  rfl
#print alloc.slice.Slice.to_vec
#print axioms complete
end R1Z.PV_RunJoin_CloneBytes43
