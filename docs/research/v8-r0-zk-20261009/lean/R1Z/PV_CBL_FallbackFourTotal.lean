import R1Z.PV_CBL_FallbackHelpersTotal
import R1Z.PV_CBL_FallbackFourModel
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_FallbackFourTotal
open PV_CBL_FallbackArray4 PV_CBL_FallbackTotal
set_option autoImplicit false
theorem total (a c w k : A4) : Total (PV_CBL_FallbackFourModel.source a c w k) := by
  obtain ⟨t,ht⟩ := PV_CBL_FallbackHelpersTotal.add w k
  obtain ⟨c',hc⟩ := PV_CBL_FallbackHelpersTotal.round c a t
  obtain ⟨u,hu⟩ := PV_CBL_FallbackHelpersTotal.swap t
  obtain ⟨a',ha⟩ := PV_CBL_FallbackHelpersTotal.round a c' u
  exact ⟨(a',c'),by simp only [PV_CBL_FallbackFourModel.source,ht,hc,hu,ha,bind_tc_ok]⟩
#print axioms total
end R1Z.PV_CBL_FallbackFourTotal
