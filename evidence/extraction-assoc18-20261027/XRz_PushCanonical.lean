import XRz_PushDomain
import XRo_Join_ResultTransport
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_PushCanonical
open S7Kani2OwnedRowRefinement
/-- No checked-overflow or independently supplied push-success premise. -/
theorem source (b : verifier.BatchedWeights) (i : Usize) (q : aspis_core.field.QM31)
 (m : U32) (x : Fin 4 → U64) (bound : i.val<b.raw.length)
 (get : b.raw.val[i.val]?=some (makeRow x))
 (canonical : ∀ k, (powerLimb (XRu_PushTransport.power q) k).val<2^31-1)
 (basis : m.val<2^31-1)
 (phase : ∀ k, S7Kani3PhaseInvariant.Phase b.terms.val (x k).val) :
 XRo_Join_Carriers.mapR XRu_PushTransport.bw (verifier.BatchedWeights.push b i q m)=
 S7Kani2OwnedPush.push_owned (XRu_PushTransport.bw b) i (XRu_PushTransport.power q) m := by
 apply XRu_PushTransport.source b i q m bound
 intro row read j raw hj hraw
 obtain ⟨r,hr,hval⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec b.raw i bound)
 have hr' : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice XRu_RowShape.Row) b.raw i=ok r := hr
 have rowEq : row=r := Result.ok.inj (read.symm.trans hr')
 have rEq : r=makeRow x := by
  have h : b.raw.val[i.val]?=some r := by
   rw [List.getElem?_eq_getElem bound]
   exact congrArg some hval.symm
  exact Option.some.inj (h.symm.trans get)
 rw [rowEq,rEq] at hraw
 exact XRz_PushDomain.row x q m b.terms.val canonical basis phase j raw hj hraw
#print axioms source
end XRz_PushCanonical
