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
abbrev low0Body := sampler.low_base_p_digits_loop0.body
abbrev low0 := sampler.low_base_p_digits_loop0
abbrev low1Body := sampler.low_base_p_digits_loop1.body
abbrev low1 := sampler.low_base_p_digits_loop1
abbrev low := sampler.low_base_p_digits
end E
namespace C
open AspisR1Post25Sampler
abbrev divBody := sampler.qm31_div_pass_loop.body
abbrev divLoop := sampler.qm31_div_pass_loop
abbrev divPass := sampler.qm31_div_pass
abbrev low0Body := sampler.low_base_p_digits_loop0.body
abbrev low0 := sampler.low_base_p_digits_loop0
abbrev low1Body := sampler.low_base_p_digits_loop1.body
abbrev low1 := sampler.low_base_p_digits_loop1
abbrev low := sampler.low_base_p_digits
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

theorem div_pass (rank : Array U32 8#usize) : E.divPass rank = C.divPass rank := by
 unfold E.divPass C.divPass XRn_Join_Release.sampler.qm31_div_pass
   AspisR1Post25Sampler.sampler.qm31_div_pass
 rw [div_loop]

theorem low0_body (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
 E.low0Body block rank i = C.low0Body block rank i := rfl

theorem low0 (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
 E.low0 block rank i = C.low0 block rank i := rfl

theorem low1_body (rank digits : Array U32 8#usize) (i : Usize) :
 E.low1Body rank digits i = C.low1Body rank digits i := by
 unfold E.low1Body C.low1Body XRn_Join_Release.sampler.low_base_p_digits_loop1.body
   AspisR1Post25Sampler.sampler.low_base_p_digits_loop1.body
 rw [div_pass]

theorem low1 (rank digits : Array U32 8#usize) (i : Usize) :
 E.low1 rank digits i = C.low1 rank digits i := by
 unfold E.low1 C.low1 XRn_Join_Release.sampler.low_base_p_digits_loop1
   AspisR1Post25Sampler.sampler.low_base_p_digits_loop1
 congr 1
 funext s
 exact low1_body s.1 s.2.1 s.2.2

theorem low (block : Array U8 32#usize) : E.low block = C.low block := by
 unfold E.low C.low XRn_Join_Release.sampler.low_base_p_digits
   AspisR1Post25Sampler.sampler.low_base_p_digits
 rw [low0,low1]

#print axioms div_body
#print axioms div_loop
#print axioms div_pass
#print axioms low0_body
#print axioms low0
#print axioms low1_body
#print axioms low1
#print axioms low
end XRo_Join_OrdinaryDigits
