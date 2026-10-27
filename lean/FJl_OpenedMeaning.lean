import FJl_OpeningBytes
import FJl_SourceSlots
import FJl_Observation
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_OpenedMeaning
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- The actual reached query and the imported backend value theorem are joined
on the SAME actual observation operands, rather than separate call witnesses. -/
theorem value (ops : Port3_NativeQueryBody.Ops) (proof : Slice U8)
    (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize) (geo : verifier.QueryGeometry)
    (b bout : verifier.BatchedWeights)
    (o : Port4C_QueryValues.Observation ops proof p a out g none geo b bout)
    (installed : ops.op20=FIp_DotsAdapter.dots)
    (hg : FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g)) :
    ∃ opening608 : Array U8 608#usize,
      opening608.val=o.opening.val.take 608 ∧
      ∀ slot : Fin 4,Port5Q1_OpeningValues.values o.dots slot=FJi_SlotValue.model opening608
        (FIp_DotsAdapter.toArray g) (Usize.ofNat slot.val (by have:=slot.isLt;scalar_tac)) := by
  have hd := o.dots_read
  rw [installed] at hd
  exact FJi_MatchingMeaning.value o.opening g o.dots hg hd
#print axioms value
end AspisR1.FJl_OpenedMeaning
end
