import NFW_PowersFrame
import NFS_QueryLoopRoot
set_option autoImplicit false
namespace AspisR1.NFW_PowersDomain
open Aeneas Aeneas.Std Result NFN_LPi_FieldValues NFW_LPi_PowersPrefix
/-- All coefficient domains are derived from the same emitted powers call. -/
theorem canonical {N : Usize} (gamma : NE) (hg : canonE gamma)
 (out : Array NE N) (run : FIo_Native.weights.powers N gamma=ok out) :
 ∀ z∈out.val,canonE z := by
 obtain ⟨actual,call,holds⟩ := NFW_LPi_PowersSource.source N gamma hg
 have same : actual=out := Result.ok.inj (call.symm.trans run)
 subst actual
 intro z hz
 obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hz
 have bound : i<N.val := by rw [←out.property];exact hi
 obtain ⟨v,hv,cv,_⟩ := holds i bound
 rw [List.getElem?_eq_getElem hi] at hv
 exact (Option.some.inj hv) ▸ cv

theorem roundtrip (x : NE) : FIo_Install.toE (FIo_Install.fromE x)=x := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
 rfl

theorem array_roundtrip {N : Usize} (out : Array NE N) :
 FIp_DotsAdapter.toArray (FIp_DotsAdapter.fromArray out)=out := by
 apply Subtype.ext
 simp only [FIp_DotsAdapter.toArray,FIp_DotsAdapter.fromArray,List.map_map]
 simpa only [Function.comp_def,roundtrip,List.map_id_fun]

/-- The exact NFS query-loop g-domain, on the same returned 29 coefficients. -/
theorem query_domain (gamma : NE) (hg : canonE gamma)
 (out : Array NE 29#usize) (run : FIo_Native.weights.powers 29#usize gamma=ok out) :
 NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray (FIp_DotsAdapter.fromArray out)) := by
 rw [array_roundtrip]
 exact canonical gamma hg out run
#print axioms canonical
#print axioms roundtrip
#print axioms array_roundtrip
#print axioms query_domain
end AspisR1.NFW_PowersDomain
