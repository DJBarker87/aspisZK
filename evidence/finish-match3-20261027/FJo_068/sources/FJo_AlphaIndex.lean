import FJc_ReadSlot
import FJo_WriterGamma
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_AlphaIndex
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- The writer's first raw alpha cell is the SAME indexed source operand. -/
theorem value (p : verifier.Prepared) (alpha : aspis_core.field.wide_exact.WideExact)
    (read : Array.index_usize p.alpha 0#usize=ok alpha) :
    (CheckpointBytes3Namespaces.toPrepared p).alpha.val[0]'(by
      simp [CheckpointBytes3Namespaces.toPrepared,CheckpointBytes3Namespaces.mapArray,p.alpha.property])=
      CheckpointBytes3Namespaces.toE alpha := by
  have cell := FJc_ReadSlot.slot _ _ _ read
  have bound : 0<p.alpha.val.length := by rw [p.alpha.property];decide
  rw [List.getElem?_eq_getElem bound] at cell
  have same : p.alpha.val[0]=alpha := Option.some.inj cell
  change (p.alpha.val.map CheckpointBytes3Namespaces.toE)[0]'_=CheckpointBytes3Namespaces.toE alpha
  rw [List.getElem_map,same]
#print axioms value
end AspisR1.FJo_AlphaIndex
end
