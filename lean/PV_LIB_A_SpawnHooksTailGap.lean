import PV_LIB_A_TypedProgramTable8
import PV_LIB_A_TypedBindingFacts
set_option autoImplicit false
namespace PV_LIB_A_SpawnHooksTailGap
open PV_STX2_Syntax PV_STX2_SliceSyntax PV_LIB_A_TypedDestruct

/-- Exact retained608 suffix drops its Option<Arc<...>> field using157, even
after successful custom Drop644. The suffix is not replaced by a unit reply. -/
theorem actual_tail : ∃ site place fn conditional unwind,
    PV_LIB_A_TypedBody608.node6 [] = .leaf (.drop site place fn conditional unwind) ∧
    PV_THR2_OffPath.functionId (.object [("Regular",fn)]) = some 157 :=
  ⟨_,_,_,_,_,rfl,rfl⟩

/-- The current SOURCE resolver has no body for the opaque generic Option glue.
A fallback P may supply it; this library has not yet discharged that obligation. -/
theorem option_source_unbound (g : Generics) :
    PV_LIB_A_TypedProgramTable8.bind 157 g = none := rfl

theorem no_option_body (g : Generics) (p : PV_STX2_SliceSyntax.Program) :
    PV_LIB_A_TypedProgramTable8.bind 157 g ≠ some p := by
  rw [option_source_unbound]
  intro h
  cases h

/-- The Arc cleanup body exists for an EXPLICIT payload/allocator pair.
This does not reconstruct an allocator from the erased Arc type. -/
theorem actual_arc_cleanup (payload allocator : Data) :
    PV_LIB_A_TypedProgramTable8.bind 405 ⟨[],[payload,allocator],[],[]⟩ =
      some (PV_LIB_A_TypedBody405.program [payload,allocator]) := rfl

#print axioms actual_tail
#print axioms option_source_unbound
#print axioms no_option_body
#print axioms actual_arc_cleanup
end PV_LIB_A_SpawnHooksTailGap
