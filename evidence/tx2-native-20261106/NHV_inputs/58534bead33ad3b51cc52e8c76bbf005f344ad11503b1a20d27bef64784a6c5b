import NHT_COMBINED_IMPORT
import NHV_NEO_ParserRef_Funs
import NHV_NEO_ParserShapes

set_option autoImplicit false
namespace NEO_ParserReference
open Aeneas Aeneas.Std Result AspisR1
abbrev E := FIo_Native.aspis_core.field.wide_exact.WideExact

/-- Exact independent extracted scalar reference and the adopted parser,
including both Option branches on arbitrary raw bytes. -/
theorem scalar (bytes : Array U8 4#usize) :
    NEO_ParserRef.m_ref bytes =
      AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes bytes := by
  rw [NBG_Atomic.m31_decode]
  simp only [NEO_ParserRef.m_ref,NEO_ParserRef.MODULUS,lift,bind_tc_ok]
  split <;> split <;> simp_all <;> omega

/-- All eight original words are returned in order on success; the lossless
observation is composed with the full emitted parser, not a success premise. -/
theorem limbs (a b c d e f g h : U32) :
    NEO_ParserRef.limbs_ref (Array.make 8#usize [a,b,c,d,e,f,g,h]) =
      (do
        let parsed ← FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
          (Array.make 8#usize [a,b,c,d,e,f,g,h])
        match parsed with
        | none => ok none
        | some value => do
          let words ← FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs value
          ok (some words)) := by
  rw [NBG_WideCarriers.limbs_result]
  simp [NEO_ParserRef.limbs_ref,NEO_ParserRef.MODULUS,Array.index_usize,
    Array.make,LPf_WideConstruction.value,NBG_WideCarriers.to_limbs_result]
  repeat' split
  all_goals simp_all
  all_goals first | omega | (subst_vars; rfl)

#print axioms scalar
#print axioms limbs
end NEO_ParserReference
