import NDO_JFr_TX2_CircleArray
import NDO_JFr_TX2_DotsBinding
import RPt_FIp_DotsOutputCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFr_TX2_CircleAfterDots
open Aeneas Aeneas.Std Result

/-- After an actual native dot return, the installed native circle call is
total without a caller canonicality premise. The dot return and geometric
inverse remain explicit; this supplies no dot result or equality gate. -/
theorem source (seed : Port3_NativeQueryBody.Ops) (i : Fin 22)
    (g : Array FIp_DotsAdapter.E 29#usize) (dots : Array FIp_DotsAdapter.E 4#usize)
    (inverse : Array U32 5#usize)
    (run : (JFr_TX2_DotsBinding.ops seed).op20 (JFo_Opening.value i) g=ok dots) :
    ∃ out, (JFr_TX2_DotsBinding.ops seed).op17 JFq_Alpha0.scalar dots inverse=ok out ∧
      Port4C_QueryArithmetic.CanonE out := by
  rw [JFr_TX2_DotsBinding.dots] at run
  have canon := FIp_DotsOutputCanonical.all _ _ _ run
  rw [JFr_TX2_DotsBinding.circle]
  apply JFr_TX2_CircleArray.source _ _ _ JFr_TX2_CircleArray.alpha0
  intro j
  exact canon _ (List.getElem_mem (by rw [dots.property];exact j.isLt))

#print axioms source
end AspisR1.JFr_TX2_CircleAfterDots
end
