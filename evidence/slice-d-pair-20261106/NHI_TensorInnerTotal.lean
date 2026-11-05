import NHI_TensorCellTotal
import NHI_Reverse
set_option autoImplicit false
noncomputable section
namespace NHI_TensorInnerTotal
open Aeneas Aeneas.Std Result ControlFlow AspisR1 LPi_FieldValues NHI_TensorCellTotal

theorem source (w : FIo_Native.weights.Weights) (k d n : Usize)
    (hk : k.val<5) (hd : d.val<5) (hn : NHI_TensorDomains.Stage n.val)
    (digitCanon : NHI_CellCanon.array
      (NHI_ScalarDomain.pick (NHI_ScalarDomain.pick w.factors k.val hk) d.val hd))
    (e : Usize) (he : e.val≤ n.val) (input : Slice NQ) (len : input.val.length=64)
    (canonical : NHI_CellCanon.slice input) :
    ∃ out,FIo_Native.weights.Weights.tensor_loop0_loop0 (NHI_Reverse.cursor e) w k input n d=
      ok (w,out) ∧ NHI_CellCanon.slice out ∧ out.val.length=64 := by
  let inv : (Rev × Slice NQ) → Prop := fun s=>s.1=NHI_Reverse.cursor s.1.iter.end ∧
    s.1.iter.end.val≤ n.val ∧ NHI_CellCanon.slice s.2 ∧ s.2.val.length=64
  let post : (FIo_Native.weights.Weights × Slice NQ) → Prop := fun s=>s.1=w ∧
    NHI_CellCanon.slice s.2 ∧ s.2.val.length=64
  have spec : WP.spec (FIo_Native.weights.Weights.tensor_loop0_loop0
      (NHI_Reverse.cursor e) w k input n d) post := by
    unfold FIo_Native.weights.Weights.tensor_loop0_loop0
    apply loop.spec_decr_nat (fun s : Rev × Slice NQ=>s.1.iter.end.val) inv post
      (fun s=>FIo_Native.weights.Weights.tensor_loop0_loop0.body w k n d s.1 s.2)
      (NHI_Reverse.cursor e,input)
    · rintro ⟨iter,arr⟩ ⟨cursor,cap,ca,size⟩
      change iter=NHI_Reverse.cursor iter.iter.end at cursor
      change iter.iter.end.val≤n.val at cap
      change NHI_CellCanon.slice arr at ca
      change arr.val.length=64 at size
      by_cases zero : iter.iter.end.val=0
      · have ez : iter.iter.end=0#usize := UScalar.eq_of_val_eq zero
        have it : iter=NHI_Reverse.cursor 0#usize := cursor.trans (congrArg NHI_Reverse.cursor ez)
        have stopped := NHI_Reverse.stop
        unfold NHI_Reverse.next at stopped
        simp only [FIo_Native.weights.Weights.tensor_loop0_loop0.body,it,stopped,bind_tc_ok]
        dsimp! only
        rw [WP.spec_ok]
        exact ⟨rfl,ca,size⟩
      · obtain ⟨j,dec,advance⟩ := NHI_Reverse.step iter.iter.end (by omega)
        have next : next iter=ok (some j,NHI_Reverse.cursor j) := by rw [cursor];exact advance
        obtain ⟨out,body,co,lo⟩ := NHI_TensorCellTotal.source w k d n j hk hd hn (by omega)
          arr size ca digitCanon iter (NHI_Reverse.cursor j) next
        rw [body,WP.spec_ok]
        change (NHI_Reverse.cursor j=NHI_Reverse.cursor j ∧ j.val≤ n.val ∧
          NHI_CellCanon.slice out ∧ out.val.length=64) ∧ j.val< iter.iter.end.val
        exact ⟨⟨rfl,by omega,co,lo⟩,by omega⟩
    · exact ⟨rfl,he,canonical,len⟩
  obtain ⟨⟨self,out⟩,run,same,co,lo⟩ := WP.spec_imp_exists spec
  change self=w at same
  subst self
  exact ⟨out,run,co,lo⟩

#print axioms source
end NHI_TensorInnerTotal
