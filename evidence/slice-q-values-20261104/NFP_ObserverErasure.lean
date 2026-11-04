import Port3_NativeQueryBody
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_ObserverErasure
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody
/-- Deployed phase observation has unit result and no model event. All
arithmetic, trace, opening and child operations retain the SAME dictionary. -/
def erase (ops : Ops) : Ops := { ops with op19 := fun _ _ => ok () }

theorem query (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (obs : Option (verifier.Phase → Result Unit)) (geometry : verifier.QueryGeometry)
 (pending : verifier.BatchedWeights) :
 verifier.candidate.query_values (erase ops) proof p a g obs geometry pending =
 verifier.candidate.query_values (erase ops) proof p a g none geometry pending := by
 rfl

theorem phase (ops : Ops) (p : verifier.Phase) :
 (erase ops).op19 none p = ok () := by rfl

theorem trace (ops : Ops) (tag : U16) (index : Usize)
 (value : aspis_core.field.wide_exact.WideExact) :
 (erase ops).op15 tag index value = ops.op15 tag index value := by rfl

#print axioms query
#print axioms phase
#print axioms trace
end AspisR1.NFP_ObserverErasure
end
