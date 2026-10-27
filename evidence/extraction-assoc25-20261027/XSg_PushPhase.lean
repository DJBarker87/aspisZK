import XSg_Sweep
import XSc_PushFrame
open Aeneas Aeneas.Std Result XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSg_PushPhase
/-- A real successful push advances the SAME cursor row, retaining the entire
raw suffix and the source term counter. No alternate successful push is assumed. -/
theorem source (b out : verifier.BatchedWeights) (i : Usize)
 (q : aspis_core.field.QM31) (m : U32) (t : Nat)
 (terms : b.terms.val=t) (bound : i.val<b.raw.length)
 (canon : XRp_PowersQAdd.CanonicalQ q) (bm : m.val<2^31-1)
 (phase : XSg_Sweep.Inv t i.val b.raw)
 (run : verifier.BatchedWeights.push b i q m=ok out) :
 XSg_Sweep.Inv t (i.val+1) out.raw ∧ out.terms=b.terms := by
 obtain ⟨⟨old,back⟩,hm,ho,hback⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.index_mut_usize_spec b.raw i bound)
 have hmut : alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice XSg_RowPhase.Row) b.raw i=ok (old,back) := by
  rw [alloc.vec.Vec.index_mut_slice_index];exact hm
 have get : b.raw.val[i.val]?=some old := by
  rw [List.getElem?_eq_getElem bound];exact congrArg some ho.symm
 have before : XSg_RowPhase.Bound b.terms.val old := by
  simpa only [Nat.lt_irrefl,if_false,terms] using phase i.val old get
 unfold verifier.BatchedWeights.push at run
 simp only [lift,bind_tc_ok,hmut] at run
 obtain ⟨row,hrow,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 have after := XSg_RowPhase.source old row q m b.terms canon bm before hrow
 rw [hback]
 exact ⟨XSg_Sweep.update t i.val b.raw row i rfl phase (by simpa only [terms] using after),rfl⟩
#print axioms source
end XSg_PushPhase
