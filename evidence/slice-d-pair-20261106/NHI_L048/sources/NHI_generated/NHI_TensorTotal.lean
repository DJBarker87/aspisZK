import NHI_TensorOuterStep
set_option autoImplicit false
noncomputable section
namespace NHI_TensorTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues
abbrev W := FIo_Native.weights.Weights
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × W × Slice NQ × Usize
abbrev Factors := NHI_TensorOuterStep.Factors

theorem outer (w : W) (k : Usize) (hk : k.val<5) (hf : Factors w)
 (input : Slice NQ) (len : input.val.length=64) (ca : NHI_CellCanon.slice input) :
 ∃ out,FIo_Native.weights.Weights.tensor_loop0 {start:=2#usize,«end»:=5#usize} w k input 1#usize=
 ok out ∧ NHI_CellCanon.slice out ∧ out.val.length=64 := by
 let inv : State → Prop := fun t=> t.1.end.val=5 ∧ t.2.1=w ∧
  NHI_TensorOuterStep.Stage t.1.start.val t.2.2.2.val ∧
  NHI_CellCanon.slice t.2.2.1 ∧ t.2.2.1.val.length=64
 let post : Slice NQ → Prop := fun out=>NHI_CellCanon.slice out ∧ out.val.length=64
 have spec : WP.spec (FIo_Native.weights.Weights.tensor_loop0
  {start:=2#usize,«end»:=5#usize} w k input 1#usize) post := by
  unfold FIo_Native.weights.Weights.tensor_loop0
  apply loop.spec_decr_nat (fun t : State=>5-t.1.start.val) inv post
   (fun t=>FIo_Native.weights.Weights.tensor_loop0.body k t.1 t.2.1 t.2.2.1 t.2.2.2)
   ({start:=2#usize,«end»:=5#usize},w,input,1#usize)
  · rintro ⟨iter,self,arr,n⟩ ⟨last,same,stage,canonical,size⟩
    change self=w at same
    subst self
    by_cases more : iter.start.val<5
    · obtain ⟨rest,out,next,run,inc,finish,st,co,lo⟩ :=
       NHI_TensorOuterStep.active w k n hk hf iter last stage more arr size canonical
      rw [run,WP.spec_ok]
      exact ⟨⟨finish,rfl,st,co,lo⟩,by omega⟩
    · rw [NHI_TensorOuterStep.done w k n iter (by omega) arr,WP.spec_ok]
      exact ⟨canonical,size⟩
  · exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩,ca,len⟩
 obtain ⟨out,run,co,lo⟩ := WP.spec_imp_exists spec
 exact ⟨out,run,co,lo⟩

#print axioms outer
end NHI_TensorTotal
end
