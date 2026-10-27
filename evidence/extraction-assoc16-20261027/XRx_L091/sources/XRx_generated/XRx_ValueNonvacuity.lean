import XRx_ValueOwned
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRx_ValueNonvacuity
/-- A genuine bounded read, for every arbitrary four-cell row and term count.
Both emitted and owned computations succeed; no accepted output is assumed. -/
theorem source (a b c d : U64) (terms : Usize) :
 ∃ q : aspis_core.field.QM31,
 verifier.BatchedWeights.value
  (⟨⟨[Array.make 4#usize [a,b,c,d]],by scalar_tac⟩,terms⟩ : verifier.BatchedWeights)
  0#usize=ok q ∧
 S8OwnedP6.value_owned (Array.make 4#usize [a,b,c,d])=ok (XRx_ValueOwned.oldQ q) := by
 let bw : verifier.BatchedWeights := ⟨⟨[Array.make 4#usize [a,b,c,d]],by scalar_tac⟩,terms⟩
 have bound : (0#usize).val<bw.raw.length := by change 0<1; omega
 obtain ⟨_,_,_,_,w,x,y,z,_,run,_,_,_,_⟩ := XRx_ValueRow.source bw 0#usize bound
 refine ⟨⟨⟨w,x⟩,⟨y,z⟩⟩,run,?_⟩
 have eq := XRx_ValueOwned.source bw 0#usize bound
 rw [run] at eq
 exact eq.symm
#print axioms source
end XRx_ValueNonvacuity
