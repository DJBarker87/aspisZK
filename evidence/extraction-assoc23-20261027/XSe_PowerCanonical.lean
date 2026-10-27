import XRy_QmMultiply
import XSc_AccumulateCuts
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_PowerCanonical
open XRp_PowersQAdd
/-- Canonical powers use the checked cohort multiplication, with no new
arithmetic correctness or successful multiplication premise. -/
theorem multiply (a b : aspis_core.field.QM31) (ha : CanonicalQ a) (hb : CanonicalQ b) :
 ∃ z, aspis_core.field.QM31.mul a b=ok z ∧ CanonicalQ z := by
 obtain ⟨z,hz,hc,_⟩ := XRy_QmMultiply.total a b ha hb
 exact ⟨z,hz,hc⟩
theorem reached (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : aspis_core.field.M31) (value : aspis_core.field.wide_exact.WideExact)
 (pending after : verifier.BatchedWeights)
 (rho : CanonicalQ p.rho) (power : CanonicalQ a.power)
 (run : verifier.accumulate_batched_with_node p a node value pending=ok (out,after)) :
 CanonicalQ out.power := by
 obtain ⟨one,basis,rows,_,_,_,hmul,_,_,_⟩ := XSc_AccumulateCuts.source p a out node value pending after run
 obtain ⟨z,hz,hc⟩ := multiply a.power p.rho power rho
 have same := Result.ok.inj (hz.symm.trans hmul)
 rw [←same]
 exact hc
#print axioms multiply
#print axioms reached
end XSe_PowerCanonical
