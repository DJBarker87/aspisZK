import NNG_PreparedQueries094
import LIBC_Geometry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_GeometryDomain094
open Aeneas Aeneas.Std Result
/-- Source k=10 and the SAME preparation result establish every input
clause of the geometry child, including uniqueness of all22 queries. -/
theorem reached (input : LIBC_PreparedLaw.Args) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (ev : List RSL.Event)
 (returned : LIBC_PreparedLaw.law input env ⟨.ret (.ok p,g),ev⟩) :
 LIBC_Geometry.Domain (p,0,10) := by
 have facts := NNG_PreparedQueries094.returned input env p g ev returned
 have zero : LIBC_Usize.raw 0=0#usize := LIBC_Usize.from_native 0#usize (by scalar_tac)
 have ten : LIBC_Usize.raw 10=10#usize := LIBC_Usize.from_native 10#usize (by scalar_tac)
 unfold LIBC_Geometry.Domain
 rw [zero,ten]
 exact ⟨rfl,rfl,Or.inl ⟨rfl,rfl⟩,facts.2,facts.1⟩
#print axioms reached
end AspisR1.NNG_GeometryDomain094
