import NGC_PreparationBoundary
import Port5Q2_Prepared
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_FieldConversion
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes3Namespaces
/-- Retained prepared fields and NGC's writer predicate have identical limbs;
only the rho predicate changes presentation to a four-index function. -/
theorem source (p : verifier.Prepared) (fields : Port5Q2_Prepared.PreparedFields p) :
 NGC_PreparationBoundary.Fields p := by
 constructor
 · change toVariant p.variant=_
   rw [fields.variant]
   rfl
 · exact fields.queries
 · exact fields.gamma
 · exact fields.kappa
 · intro j
   simp only [toPrepared,mapArray,List.getElem_map]
   exact fields.alpha j
 · intro j
   fin_cases j
   · exact fields.rho.1
   · exact fields.rho.2.1
   · exact fields.rho.2.2.1
   · exact fields.rho.2.2.2
 · intro j
   simp only [toPrepared,mapArray,List.getElem_map]
   exact fields.semanticAlpha j
 · intro j
   have h:=fields.coordinates j
   fin_cases j <;> simpa only [toPrepared,mapArray,List.getElem_map,toPoint] using h
 · exact fields.claim
#print axioms source
end AspisR1.NHS_FieldConversion
