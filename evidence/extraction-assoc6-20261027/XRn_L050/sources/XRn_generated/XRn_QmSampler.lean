import XRn_Transcript
import XRn_ResultTransport
open Aeneas Aeneas.Std Result
open XRn_Carriers XRn_ResultTransport
set_option autoImplicit false
namespace XRn_QmSampler
namespace R
open XRk_Release
abbrev divBody := sampler.qm31_div_pass_loop.body
abbrev divLoop := sampler.qm31_div_pass_loop
abbrev divPass := sampler.qm31_div_pass
abbrev digits0Body := sampler.qm31_digits_loop0.body
abbrev digits0 := sampler.qm31_digits_loop0
abbrev digits1Body := sampler.qm31_digits_loop1.body
abbrev digits1 := sampler.qm31_digits_loop1
abbrev digits := sampler.qm31_digits
end R
namespace O
open AspisR1PublicPreparation
abbrev divBody := sampler.qm31_div_pass_loop.body
abbrev divLoop := sampler.qm31_div_pass_loop
abbrev divPass := sampler.qm31_div_pass
abbrev digits0Body := sampler.qm31_digits_loop0.body
abbrev digits0 := sampler.qm31_digits_loop0
abbrev digits1Body := sampler.qm31_digits_loop1.body
abbrev digits1 := sampler.qm31_digits_loop1
abbrev digits := sampler.qm31_digits
end O

theorem div_body (rank : Array U32 8#usize) (rem : U64) (j : Usize) :
 R.divBody rank rem j=O.divBody rank rem j := by
 unfold R.divBody O.divBody XRk_Release.sampler.qm31_div_pass_loop.body AspisR1PublicPreparation.sampler.qm31_div_pass_loop.body
 simp only [aspis_core.field.P,bind_tc_ok]
 rfl

theorem div_loop (rank : Array U32 8#usize) (rem : U64) (j : Usize) :
 R.divLoop rank rem j=O.divLoop rank rem j := by
 unfold R.divLoop O.divLoop XRk_Release.sampler.qm31_div_pass_loop AspisR1PublicPreparation.sampler.qm31_div_pass_loop
 congr 1
 funext s
 exact div_body s.1 s.2.1 s.2.2

theorem div_pass (rank : Array U32 8#usize) : R.divPass rank=O.divPass rank := by
 unfold R.divPass O.divPass XRk_Release.sampler.qm31_div_pass AspisR1PublicPreparation.sampler.qm31_div_pass
 rw [div_loop]

theorem digits0_body (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
 R.digits0Body block rank i=O.digits0Body block rank i := rfl

theorem digits0 (block : Array U8 32#usize) (rank : Array U32 8#usize) (i : Usize) :
 R.digits0 block rank i=O.digits0 block rank i := by
 unfold R.digits0 O.digits0 XRk_Release.sampler.qm31_digits_loop0 AspisR1PublicPreparation.sampler.qm31_digits_loop0
 congr 1
 funext s
 exact digits0_body block s.1 s.2

theorem digits1_body (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
 R.digits1Body rank digits i=O.digits1Body rank digits i := by
 unfold R.digits1Body O.digits1Body XRk_Release.sampler.qm31_digits_loop1.body AspisR1PublicPreparation.sampler.qm31_digits_loop1.body
 simp only [div_pass]

theorem digits1 (rank : Array U32 8#usize) (digits : Array U32 4#usize) (i : Usize) :
 R.digits1 rank digits i=O.digits1 rank digits i := by
 unfold R.digits1 O.digits1 XRk_Release.sampler.qm31_digits_loop1 AspisR1PublicPreparation.sampler.qm31_digits_loop1
 congr 1
 funext s
 exact digits1_body s.1 s.2.1 s.2.2

theorem digits (block : Array U8 32#usize) : R.digits block=O.digits block := by
 unfold R.digits O.digits XRk_Release.sampler.qm31_digits AspisR1PublicPreparation.sampler.qm31_digits
 simp only [digits0,digits1]

theorem sample (block : Array U8 32#usize) :
 mapR cq (XRk_Release.sampler.qm31_sample block)=AspisR1PublicPreparation.sampler.qm31_sample block := by
 unfold XRk_Release.sampler.qm31_sample AspisR1PublicPreparation.sampler.qm31_sample
 simp only [digits,mapR_bind,map_ok,
   aspis_core.field.CM31.new,AspisR1PublicPreparation.aspis_core.field.CM31.new,bind_tc_ok]
 rfl

#print axioms div_body
#print axioms div_loop
#print axioms div_pass
#print axioms digits0_body
#print axioms digits0
#print axioms digits1_body
#print axioms digits1
#print axioms digits
#print axioms sample
end XRn_QmSampler
