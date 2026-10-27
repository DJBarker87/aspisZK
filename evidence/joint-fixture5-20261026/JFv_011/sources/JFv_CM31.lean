import JFv_M31
import R1CandidateCM31Parser
set_option autoImplicit false
namespace AspisR1.JFv_CM31
open Aeneas Aeneas.Std Result
open AspisR1DecodeKFullV10
open CandidateCM31Parser

theorem success (arr : Array U8 8#usize)
    (h0 : (core.num.U32.from_le_bytes (half0 arr)).val < 2147483647)
    (h1 : (core.num.U32.from_le_bytes (half1 arr)).val < 2147483647) :
    aspis_core.field.CM31.from_le_bytes (Array.to_slice arr) =
      ok (some ⟨core.num.U32.from_le_bytes (half0 arr),core.num.U32.from_le_bytes (half1 arr)⟩) := by
  have s0 := ParserArraySlice.slice_segment arr 0#usize 4#usize (by decide) 4#usize (by decide)
  have s1 := ParserArraySlice.slice_segment arr 4#usize 4#usize (by decide) 8#usize (by decide)
  change _ = ok (Array.to_slice (half0 arr)) at s0
  change _ = ok (Array.to_slice (half1 arr)) at s1
  have p0 := JFv_M31.success (half0 arr) h0
  have p1 := JFv_M31.success (half1 arr) h1
  simp only [aspis_core.field.CM31.from_le_bytes,s0,s1,
    AspisV8R19.SamplerWordRead.conversion_success,p0,p1,bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]

#print axioms success
end AspisR1.JFv_CM31
