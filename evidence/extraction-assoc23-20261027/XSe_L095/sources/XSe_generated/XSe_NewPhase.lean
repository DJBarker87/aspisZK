import XSe_InitialRowPhase
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_NewPhase
open XRu_NewStep
theorem step (weights : Slice aspis_core.field.QM31) (s : S)
 (r : ControlFlow S Raw) (inv : Inv weights s) (small : XSe_InitialRowPhase.Small s.1)
 (run : verifier.BatchedWeights.new_loop.body weights s.1 s.2=ok r) :
 match r with
 | .done out => XSe_InitialRowPhase.Small out
 | .cont next => XSe_InitialRowPhase.Small next.1 := by
 rcases s with ⟨raw,index⟩
 rcases inv with ⟨len,bound⟩
 change raw.val.length=weights.val.length at len
 change index.val≤weights.val.length at bound
 unfold verifier.BatchedWeights.new_loop.body at run
 dsimp only at run
 split at run
 · rename_i active
   change index.val<weights.val.length at active
   obtain ⟨w,_,run⟩ := bind_success _ _ _ run
   simp only [lift,bind_tc_ok] at run
   obtain ⟨old,back,hmut,run⟩ := pair_bind_success _ _ _ run
   obtain ⟨⟨old1,back1⟩,hm,ho,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec raw index (by change index.val<raw.val.length; omega))
   have hm' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) raw index=ok (old1,back1) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hm
   cases Result.ok.inj (hm'.symm.trans hmut)
   obtain ⟨next,hn,run⟩ := bind_success _ _ _ run
   cases Result.ok.inj run
   change XSe_InitialRowPhase.Small (back _)
   rw [hback]
   exact XSe_InitialRowPhase.set raw index w small
 · cases Result.ok.inj run
   exact small

theorem loop (weights : Slice aspis_core.field.QM31) (raw out : Raw) (i : Usize)
 (inv : Inv weights (raw,i)) (small : XSe_InitialRowPhase.Small raw)
 (run : verifier.BatchedWeights.new_loop weights raw i=ok out) : XSe_InitialRowPhase.Small out := by
 unfold verifier.BatchedWeights.new_loop at run
 apply XRl_LoopInvariant.preserve _
  (fun s : S => Inv weights s ∧ XSe_InitialRowPhase.Small s.1)
  XSe_InitialRowPhase.Small (measure weights) ?_ (raw,i) out ⟨inv,small⟩ run
 intro s r hs hr
 have safety := step weights s r hs.1 hs.2 hr
 have shape := XRu_NewStep.source weights s r hs.1 hr
 cases r with
 | done out => exact safety
 | cont next => exact ⟨⟨shape.1,safety⟩,shape.2⟩
#print axioms step
#print axioms loop
end XSe_NewPhase
