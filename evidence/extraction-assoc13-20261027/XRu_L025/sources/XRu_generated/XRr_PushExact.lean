import XRr_PushFrame
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRr_PushExact
/-- The mutable-element wrapper is one concrete set, provided THIS row call
returns. It asserts no alternate execution or native attribution. -/
theorem returned (b : verifier.BatchedWeights) (i : Usize)
 (power : aspis_core.field.QM31) (basis : aspis_core.field.M31)
 (bound : i.val<b.raw.length) (row : Array U64 4#usize)
 (hrow : verifier.update_residue_row
   b.raw.val[i.val] power basis ((b.terms &&& 3#usize)=3#usize)=ok row) :
 verifier.BatchedWeights.push b i power basis=ok {b with raw:=b.raw.set i row} := by
 obtain ⟨⟨old,back⟩,hm,ho,hback⟩ := WP.spec_imp_exists
   (alloc.vec.Vec.index_mut_usize_spec b.raw i bound)
 have hmut : alloc.vec.Vec.index_mut
   (core.slice.index.SliceIndexUsizeSlice (Array U64 4#usize)) b.raw i=ok (old,back) := by
   rw [alloc.vec.Vec.index_mut_slice_index]
   exact hm
 have same : old=b.raw.val[i.val] := ho
 simp only [verifier.BatchedWeights.push,lift,bind_tc_ok,hmut]
 change (do
   let updated ← verifier.update_residue_row old power basis ((b.terms &&& 3#usize)=3#usize)
   ok ({raw:=back updated,terms:=b.terms} : verifier.BatchedWeights)) = _
 rw [same,hrow]
 simp only [bind_tc_ok,hback]
#print axioms returned
end XRr_PushExact
