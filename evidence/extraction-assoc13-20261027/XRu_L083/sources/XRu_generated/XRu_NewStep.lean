import XRu_RowBoth
import XRr_Initial64
import XRl_LoopInvariant
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRu_NewStep
abbrev Raw := alloc.vec.Vec (Array U64 4#usize)
abbrev S := Raw × Usize
def Inv (weights : Slice aspis_core.field.QM31) (s : S) : Prop :=
 s.1.val.length=weights.val.length ∧ s.2.val≤weights.val.length
def measure (weights : Slice aspis_core.field.QM31) (s : S) : Nat := weights.val.length-s.2.val
theorem source (weights : Slice aspis_core.field.QM31) (s : S)
 (r : ControlFlow S Raw) (inv : Inv weights s)
 (run : verifier.BatchedWeights.new_loop.body weights s.1 s.2=ok r) :
 match r with
 | .done out => out.val.length=weights.val.length
 | .cont next => Inv weights next ∧ measure weights next<measure weights s := by
 rcases s with ⟨raw,index⟩
 rcases inv with ⟨len,bound⟩
 unfold verifier.BatchedWeights.new_loop.body at run
 dsimp only at run
 split at run
 · rename_i active
   obtain ⟨w,_,run⟩ := bind_success _ _ _ run
   simp only [lift,bind_tc_ok] at run
   obtain ⟨old,back,hmut,run⟩ := pair_bind_success _ _ _ run
   obtain ⟨⟨old1,back1⟩,hm,ho,hback⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_mut_usize_spec raw index (by change index.val<weights.val.length at active; omega))
   have hm' : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) raw index=ok (old1,back1) := by
    rw [alloc.vec.Vec.index_mut_slice_index]
    exact hm
   cases Result.ok.inj (hm'.symm.trans hmut)
   obtain ⟨next,hn,run⟩ := bind_success _ _ _ run
   cases Result.ok.inj run
   have he : next.val=index.val+1 := by
    obtain ⟨n,hadd,hval⟩ := AspisR1.ExtractedCurrentReducerOps.add_success index 1#usize (by scalar_tac)
    have same := Result.ok.inj (hadd.symm.trans hn)
    simpa only [same] using hval
   simp only [Inv,measure,hback]
   have lset : (raw.set index (Array.make 4#usize [UScalar.cast .U64 w.c0.a,UScalar.cast .U64 w.c0.b,UScalar.cast .U64 w.c1.a,UScalar.cast .U64 w.c1.b])).val.length=raw.val.length := by
    simp [alloc.vec.Vec.set]
   exact ⟨⟨lset.trans len,by omega⟩,by omega⟩
 · cases Result.ok.inj run
   exact len
#print axioms source
end XRu_NewStep
