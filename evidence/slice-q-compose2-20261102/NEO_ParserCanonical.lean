import NEO_ParserTotal
set_option autoImplicit false
namespace NEO_ParserCanonical
open Aeneas Aeneas.Std Result AspisR1

/-- Acceptance derives the scalar callee's canonical output domain; the input
bytes remain completely unrestricted. -/
theorem scalar (bytes : Array U8 4#usize) (value : U32)
    (run : AspisR1TerminalDecoder.aspis_core.field.M31.from_le_bytes bytes=ok (some value)) :
    value.val<2147483647 := by
  rw [NBG_Atomic.m31_decode] at run
  dsimp only at run
  split at run
  · simp_all
  · have same := Option.some.inj (Result.ok.inj run)
    subst value
    scalar_tac

/-- Every accepted raw array supplies canonical nested field coordinates.
Neither acceptance nor canonicality is added as a root input restriction. -/
theorem wide (xs : Array U32 8#usize) (value : NEO_ParserTotal.E)
    (run : FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs xs=ok (some value)) :
    LPi_FieldValues.canonE value := by
  obtain ⟨a,b,c,d,e,f,g,h,rfl⟩ := NEO_ParserTotal.eight xs
  rw [NBG_WideCarriers.limbs_result] at run
  split at run
  · have same := Option.some.inj (Result.ok.inj run)
    subst value
    simp_all [LPi_FieldValues.canonE,LPi_FieldValues.canonQ,LPi_FieldValues.canonC,LPi_CMProduct.Canon,
      LPf_WideConstruction.value]
  · simp_all

#print axioms scalar
#print axioms wide
end NEO_ParserCanonical
