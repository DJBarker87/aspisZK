import R1Z.PV_RunJoin_WeightInstalled46
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_CloneQ66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
abbrev Q := aspis_core.field.QM31

theorem scalar (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (q : Q) :
    @aspis_core.field.QM31.Insts.CoreCloneClone.clone (types base) (selected base heap box ops) q=ok q := by
  change (selected base heap box ops).op62 q=ok q
  unfold selected
  rw [PV_B2_F_RawNative.preserved_62]
  rfl

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (s : Slice Q) :
    @alloc.slice.Slice.to_vec Q
      (@aspis_core.field.QM31.Insts.CoreCloneClone (types base) (selected base heap box ops)) s=
      ok (⟨s.val,s.property⟩ : alloc.vec.Vec Q) := by
  let clone := @aspis_core.field.QM31.Insts.CoreCloneClone.clone (types base) (selected base heap box ops)
  have hclone : Slice.clone clone s=ok s := by
    obtain ⟨s',heq,hs⟩ := WP.spec_imp_exists
      (Slice.clone_spec (s := s) (clone := clone) (by intro x _;exact scalar base heap box ops x))
    simpa only [←hs] using heq
  simp only [alloc.slice.Slice.to_vec]
  rw [hclone]
  rfl

#print axioms scalar
#print axioms complete
end R1Z.PV_RunJoin_CloneQ66
