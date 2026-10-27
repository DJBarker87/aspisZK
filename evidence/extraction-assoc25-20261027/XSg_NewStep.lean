import XSg_NewRows
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSg_NewStep
open XSg_NewRows XRu_NewStep
/-- The actual constructor loop installs exactly the SAME source weight at
its current cursor, preserving the already installed prefix. -/
theorem source (weights : Slice Q) (s : S) (r : ControlFlow S Raw)
 (inv : Inv weights s) (built : Built weights s.1 s.2.val)
 (run : verifier.BatchedWeights.new_loop.body weights s.1 s.2=ok r) :
 match r with
 | .done out => out.val=weights.val.map row
 | .cont next => Built weights next.1 next.2.val := by
 rcases s with ⟨raw,index⟩
 rcases inv with ⟨len,bound⟩
 dsimp only at len bound built ⊢
 unfold verifier.BatchedWeights.new_loop.body at run
 dsimp only at run
 split at run
 · rename_i active
   change index.val<weights.val.length at active
   obtain ⟨w,hw,run⟩ := bind_success _ _ _ run
   obtain ⟨x,hx,hval⟩ := WP.spec_imp_exists (Slice.index_usize_spec weights index active)
   have same : x=w := Result.ok.inj (hx.symm.trans hw)
   have get : weights.val[index.val]?=some w := by
    rw [List.getElem?_eq_getElem active];exact congrArg some (same.symm.trans hval)
   simp only [lift,bind_tc_ok] at run
   obtain ⟨old,back,hmut,run⟩ := pair_bind_success _ _ _ run
   have rb : index.val<raw.val.length := by omega
   obtain ⟨⟨old1,back1⟩,hm,ho,hback⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_mut_usize_spec raw index rb)
   have hm' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice XSg_RowPhase.Row) raw index=ok (old1,back1) := by
    rw [alloc.vec.Vec.index_mut_slice_index];exact hm
   cases Result.ok.inj (hm'.symm.trans hmut)
   obtain ⟨next,hn,run⟩ := bind_success _ _ _ run
   cases Result.ok.inj run
   have spec : (index+1#usize : Result Usize) ⦃ n => n.val=index.val+1 ⦄ := by
    apply UScalar.add_spec;have := weights.property;scalar_tac
   obtain ⟨n,hadd,hv⟩ := WP.spec_imp_exists spec
   have ne := Result.ok.inj (hadd.symm.trans hn)
   have inc : next.val=index.val+1 := by simpa only [ne] using hv
   change Built weights (back (row w)) next.val
   rw [hback,inc]
   exact XSg_NewRows.set weights raw index w built rb get
 · rename_i done
   cases Result.ok.inj run
   have last : index.val=weights.val.length := by change ¬ index.val<weights.val.length at done;omega
   exact XSg_NewRows.final weights raw len (by simpa only [last] using built)
#print axioms source
end XSg_NewStep
