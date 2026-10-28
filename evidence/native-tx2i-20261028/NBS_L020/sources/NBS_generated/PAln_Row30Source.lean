import PAln_RootConvert
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Row30Source
open MultiproofConeCanonical OraclePortCompactDraft

theorem extend (before out : alloc.vec.Vec U8) (payload : Slice U8)
    (call : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 before payload=ok out) :
    out.val=before.val++payload.val := by
  obtain ⟨copy,cloned,same⟩ := WP.spec_imp_exists (Slice.clone_spec (s:=payload)
    (clone:=(liftFun1 core.clone.impls.CloneU8.clone)) (by intro x member;rfl))
  have cloned' : Slice.clone (liftFun1 core.clone.impls.CloneU8.clone) payload=ok payload := by
    simpa only [←same] using cloned
  unfold alloc.vec.Vec.extend_from_slice at call
  split at call
  · split at call
    · rename_i s heq
      have eq : s=payload := Result.ok.inj (heq.symm.trans cloned')
      subst s
      exact (congrArg Subtype.val (Result.ok.inj call)).symm
    · rename_i e heq
      rw [cloned'] at heq
      cases heq
    · rename_i heq
      rw [cloned'] at heq
      cases heq
  · cases call

theorem bytes (proof semantic y1 : Slice U8) (view : AspisR1SelectedWideViewV1.verifier.View)
    (accepted : AspisR1SelectedWideViewV1.verifier.candidate.wide_view proof semantic y1=ok (.Ok view))
    (root : Array U8 32#usize) (bytes1 bytes2 : alloc.vec.Vec U8)
    (unwrapped : core.option.Option.unwrap view.folded_root=ok root)
    (first : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
      (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root)=ok bytes1)
    (second : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 view.round1=ok bytes2) :
    bytesOf bytes2.val=slice (bytesOf proof.val) 7751 256 := by
  obtain ⟨sourceRoot,sourceEq,sourceBytes⟩ := PAln_RootConvert.source proof semantic y1 view accepted
  rw [sourceEq] at unwrapped
  have rootEq : sourceRoot=root := Result.ok.inj unwrapped
  subst sourceRoot
  have sections := PAln_Physical.opening_sections proof semantic y1 view accepted
  have firstBytes := extend _ _ _ first
  have secondBytes := extend _ _ _ second
  have split : slice (bytesOf proof.val) 7751 256=
      slice (bytesOf proof.val) 7751 32++slice (bytesOf proof.val) 7783 224 := by
    change ((bytesOf proof.val).drop 7751).take (32+224)=_
    rw [List.take_add]
    simp only [slice,List.drop_drop]
  rw [secondBytes,firstBytes]
  change bytesOf ([]++root.val++view.round1.val)=_
  rw [List.nil_append,show bytesOf (root.val++view.round1.val)=bytesOf root.val++bytesOf view.round1.val from List.map_append,
    sourceBytes,sections.2.1,split]

#print axioms extend
#print axioms bytes
end AspisR1.PAln_Row30Source
