import RPt_JFn_Values
import JFn_LineArrayTotal
import NDO_JFn_AlphaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_Lines
open Aeneas Aeneas.Std Result

/-- Native line evaluation returns on every real TX2 value array. Geometry
and the preceding circle-fold equality gate are outside this local theorem. -/
theorem source (i : Fin 12) (inverse : Array U32 5#usize) :
    ∃ out, SAQ_LineQuery.line JFq_Alpha1.scalar (JFn_Values.value i) inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out :=
  JFn_LineArrayTotal.source _ _ inverse JFn_AlphaCanonical.alpha1 (JFn_Values.canonical i)

#print axioms source
end AspisR1.JFn_Lines
end
