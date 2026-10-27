import XRo_Join_PreparedScalars
import CurrentSamplerOrdinaryCallbackV2
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRo_Join_OrdinaryDigits
namespace E
open XRn_Join_Release
abbrev divBody := sampler.qm31_div_pass_loop.body
abbrev divLoop := sampler.qm31_div_pass_loop
abbrev divPass := sampler.qm31_div_pass
end E
namespace C
open AspisR1Post25Sampler
abbrev divBody := sampler.qm31_div_pass_loop.body
abbrev divLoop := sampler.qm31_div_pass_loop
abbrev divPass := sampler.qm31_div_pass
end C

theorem div_body (rank : Array U32 8#usize) (rem : U64) (j : Usize) :
 E.divBody rank rem j = C.divBody rank rem j := by
 unfold E.divBody C.divBody XRn_Join_Release.sampler.qm31_div_pass_loop.body
   AspisR1Post25Sampler.sampler.qm31_div_pass_loop.body
 simp only [aspis_core.field.P, AspisR1Post25Sampler.field.P, bind_tc_ok]

theorem div_loop (rank : Array U32 8#usize) (rem : U64) (j : Usize) :
 E.divLoop rank rem j = C.divLoop rank rem j := by
 unfold E.divLoop C.divLoop XRn_Join_Release.sampler.qm31_div_pass_loop
   AspisR1Post25Sampler.sampler.qm31_div_pass_loop
 congr 1
 funext s
 exact div_body s.1 s.2.1 s.2.2

#print axioms div_body
#print axioms div_loop
end XRo_Join_OrdinaryDigits
