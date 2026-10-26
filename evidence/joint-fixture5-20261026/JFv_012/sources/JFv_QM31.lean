import JFv_CM31
import R1CandidateQM31Parser
set_option autoImplicit false
namespace AspisR1.JFv_QM31
open Aeneas Aeneas.Std Result
open AspisR1DecodeKFullV10

def word (arr : Array U8 16#usize) (high low : Bool) : Array U8 4#usize :=
  let half := if high then CandidateQM31Parser.half1 arr else CandidateQM31Parser.half0 arr
  if low then CandidateCM31Parser.half1 half else CandidateCM31Parser.half0 half

def value (arr : Array U8 16#usize) : aspis_core.field.QM31 :=
  ⟨⟨core.num.U32.from_le_bytes (word arr false false),core.num.U32.from_le_bytes (word arr false true)⟩,
   ⟨core.num.U32.from_le_bytes (word arr true false),core.num.U32.from_le_bytes (word arr true true)⟩⟩

theorem success (arr : Array U8 16#usize)
    (canonical : ∀ high low,(core.num.U32.from_le_bytes (word arr high low)).val < 2147483647) :
    aspis_core.field.QM31.from_le_bytes (Array.to_slice arr)=ok (some (value arr)) := by
  have s0 := ParserArraySlice.slice_segment arr 0#usize 8#usize (by decide) 8#usize (by decide)
  have s1 := ParserArraySlice.slice_segment arr 8#usize 8#usize (by decide) 16#usize (by decide)
  change _ = ok (Array.to_slice (CandidateQM31Parser.half0 arr)) at s0
  change _ = ok (Array.to_slice (CandidateQM31Parser.half1 arr)) at s1
  have p0 := JFv_CM31.success (CandidateQM31Parser.half0 arr) (canonical false false) (canonical false true)
  have p1 := JFv_CM31.success (CandidateQM31Parser.half1 arr) (canonical true false) (canonical true true)
  simp only [aspis_core.field.QM31.from_le_bytes,s0,s1,p0,p1,bind_tc_ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch]
  rfl

#print axioms success
end AspisR1.JFv_QM31
