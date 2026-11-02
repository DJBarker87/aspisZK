import NEI_WideCtorRaw.Funs
import NEI_WideCtorLaw
set_option autoImplicit false
noncomputable section
namespace NEI_WideCtorAssociation
open Aeneas Aeneas.Std Result
abbrev R := NEI_WideCtorRaw.aspis_core.field.wide_exact.WideExact
abbrev E := NEI_WideCtorLaw.E
def toE (x : R) : E :=
 ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
  ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
/-- Actual emitted guard order, Option tag and every coordinate, with raw U32s. -/
theorem same_result (a b c d e f g h : U32) :
 (do let out ← NEI_WideCtorRaw.aspis_core.field.wide_exact.WideExact.from_limbs
       (Array.make 8#usize [a,b,c,d,e,f,g,h]); ok (out.map toE)) =
 FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs
       (Array.make 8#usize [a,b,c,d,e,f,g,h]) := by
 simp [NEI_WideCtorRaw.aspis_core.field.wide_exact.WideExact.from_limbs,
  FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs,
  NEI_WideCtorRaw.aspis_core.field.P,FIo_Native.aspis_core.field.P,
  Array.index_usize,Array.make,toE]
 repeat' split
 all_goals rfl
#print axioms same_result
end NEI_WideCtorAssociation
end
