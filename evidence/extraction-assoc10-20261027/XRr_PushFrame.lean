import XRn_Join_Funs
import XRk_ResultTools
open Aeneas Aeneas.Std Result
open XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XRr_PushFrame
/-- The query counter is incremented by the caller, never a row push. -/
theorem terms (b out : verifier.BatchedWeights) (i : Usize)
 (power : aspis_core.field.QM31) (basis : aspis_core.field.M31)
 (h : verifier.BatchedWeights.push b i power basis=ok out) : out.terms=b.terms := by
 unfold verifier.BatchedWeights.push at h
 obtain ⟨phase,_,h⟩ := bind_success _ _ _ h
 obtain ⟨cell,restore,_,h⟩ := pair_bind_success _ _ _ h
 obtain ⟨row,_,h⟩ := bind_success _ _ _ h
 cases Result.ok.inj h
 rfl
#print axioms terms
end XRr_PushFrame
