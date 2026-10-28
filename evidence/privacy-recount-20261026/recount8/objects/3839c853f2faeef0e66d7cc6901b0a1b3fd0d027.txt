import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteAppend38
open Aeneas Aeneas.Std Result

theorem append (out : alloc.vec.Vec U8) (s : Slice U8)
    (room : out.length + s.length ≤ Usize.max) :
    ∃ next, alloc.vec.Vec.extend_from_slice core.clone.CloneU8 out s = .ok next ∧
      next.val = out.val ++ s.val := by
  have hclone : Slice.clone core.clone.CloneU8.clone s = .ok s := by
    obtain ⟨s', heq, hs⟩ := WP.spec_imp_exists
      (Slice.clone_spec (s := s) (clone := core.clone.CloneU8.clone)
        (by intro x _; rfl))
    simpa only [← hs] using heq
  change Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) s = .ok s at hclone
  refine ⟨⟨out.val ++ s.val, by simpa only [List.length_append] using room⟩, ?_, rfl⟩
  simp only [alloc.vec.Vec.extend_from_slice, dif_pos room]
  split
  · rename_i s' hs'
    have same : s' = s := Result.ok.inj (hs'.symm.trans hclone)
    subst s'
    rfl
  · rename_i e he
    have impossible : fail e = .ok s := he.symm.trans hclone
    cases impossible
  · rename_i he
    have impossible : (div : Result (Slice U8)) = .ok s := he.symm.trans hclone
    cases impossible

#print axioms append
end R1Z.PV_RunJoin_ByteAppend38
