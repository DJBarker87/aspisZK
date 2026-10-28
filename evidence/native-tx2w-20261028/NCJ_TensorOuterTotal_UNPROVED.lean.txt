import NCJ_TensorOuterStep
set_option autoImplicit false
noncomputable section
namespace NCJ_TensorOuterTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues NCJ_TensorOuterStep

theorem source (w : W) (k n : Usize) (hk : k.val<5) (hf : Factors w)
    (iter : Iter) (he : iter.end.val=5) (stage : Stage iter.start.val n.val)
    (input : Slice NQ) (len : input.val.length=64) (ca : NCJ_CellCanon.slice input) :
    ∃ out,FIo_Native.weights.Weights.tensor_loop0 iter w k input n=ok out ∧
      NCJ_CellCanon.slice out ∧ out.val.length=64 := by
  let inv : (Iter × W × Slice NQ × Usize) → Prop := fun s=>s.1.end.val=5 ∧
    s.2.1=w ∧ Stage s.1.start.val s.2.2.2.val ∧
    NCJ_CellCanon.slice s.2.2.1 ∧ s.2.2.1.val.length=64
  let post : Slice NQ → Prop := fun s=>NCJ_CellCanon.slice s ∧ s.val.length=64
  have spec : WP.spec (FIo_Native.weights.Weights.tensor_loop0 iter w k input n) post := by
    unfold FIo_Native.weights.Weights.tensor_loop0
    apply loop.spec_decr_nat (fun s : Iter × W × Slice NQ × Usize=>5-s.1.start.val)
      inv post (fun s=>body k s.1 s.2.1 s.2.2.1 s.2.2.2) (iter,w,input,n)
    · rintro ⟨cursor,self,arr,width⟩ ⟨end5,same,st,canon,size⟩
      change cursor.end.val=5 at end5
      change self=w at same
      change Stage cursor.start.val width.val at st
      change NCJ_CellCanon.slice arr at canon
      change arr.val.length=64 at size
      dsimp! only
      by_cases more : cursor.start.val<5
      · obtain ⟨rest,out,next,run,inc,end5,st,co,lo⟩ := active w k width hk hf cursor end5 st more arr size canon
        have original := (congrArg (fun receiver => body k cursor receiver arr width) same).trans run
        unfold body at original
        with_unfolding_all rw [original,WP.spec_ok]
        change (rest.end.val=5 ∧ w=w ∧ Stage rest.start.val next.val ∧
          NCJ_CellCanon.slice out ∧ out.val.length=64) ∧ 5-rest.start.val<5-cursor.start.val
        exact ⟨⟨end5,rfl,st,co,lo⟩,by omega⟩
      · with_unfolding_all rw [done self k width cursor (by omega) arr,WP.spec_ok]
        exact ⟨canon,size⟩
    · exact ⟨he,rfl,stage,ca,len⟩
  exact WP.spec_imp_exists spec
#print axioms source
end NCJ_TensorOuterTotal
