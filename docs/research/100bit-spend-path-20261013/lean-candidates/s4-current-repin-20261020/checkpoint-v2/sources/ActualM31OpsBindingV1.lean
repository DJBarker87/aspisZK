import AspisR1FastDotsCurrent.FunsOpsV4
import AspisR1DecodeKFullV10ParserCanonicality
import ExtractedCurrentReducer

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsCurrentM31OpsBinding

abbrev Ops := AspisR1FastDotsCurrent.FourDotsOps
abbrev M31 := AspisR1FastDotsCurrent.aspis_core.field.M31

/-- Bind the emitted parser/reducer slots to the retained source-shaped
    implementations. Every other operation stays a caller-supplied boundary. -/
def withCurrentM31ParserReducer (ops : Ops) : Ops :=
  { ops with
    m31FromBytes := AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes
    m31ReduceU64 := AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 }

theorem parser_binding (ops : Ops) (bytes : Array U8 4#usize) :
    (withCurrentM31ParserReducer ops).m31FromBytes bytes =
      AspisR1DecodeKFullV10.aspis_core.field.M31.from_le_bytes bytes := rfl

theorem parser_success_canonical (ops : Ops) (bytes : Array U8 4#usize)
    (x : M31)
    (h : (withCurrentM31ParserReducer ops).m31FromBytes bytes = .ok (some x)) :
    x.val < AspisR1DecodeKFullV10.aspis_core.field.P.val := by
  exact AspisR1DecodeKFullV10ParserCanonicality.m31_from_le_bytes_success_canonical
    bytes x h

theorem reducer_binding (ops : Ops) (x : U64) :
    (withCurrentM31ParserReducer ops).m31ReduceU64 x =
      AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x := rfl

theorem reducer_success_mod (ops : Ops) (x : U64) (z : M31)
    (h : (withCurrentM31ParserReducer ops).m31ReduceU64 x = .ok z) :
    z.val = x.val % AspisV8R17.RawReducer.P ∧
      z.val < AspisV8R17.RawReducer.P := by
  have hactual : AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x = .ok z := by
    simpa only [reducer_binding] using h
  obtain ⟨z0, hz0, hmod, hcanonical⟩ :=
    AspisR1.ExtractedCurrentReducer.current_wrapper_mod x
  rw [hz0] at hactual
  cases hactual
  exact ⟨hmod, hcanonical⟩

#print axioms parser_success_canonical
#print axioms reducer_success_mod

end AspisR1FastDotsCurrentM31OpsBinding
