import PV_B3P_WholeBuffer226
import PV_B3P_Install226V3
import PV_B3P_ProjectV3Law226
namespace PV_B3P_InstalledBuffer226
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

theorem reference_value (p : PV_B3P_226V3.reference226.Source)
    (chunks : PV_B3P_ByteOutput226.Chunks) (n : Usize)
    (h : PV_B3P_226V3.reference226.public_bytes p = .ok (.Ok (chunks,n))) :
    (PV_B3P_ByteOutput226.bytes chunks n).val =
      PV_B3P_ByteLayout226V3.layout (PV_B3P_ProjectV3Law226.value p) := by
  rw [PV_B3P_ProjectV3Law226.complete_source] at h
  exact PV_B3P_WholeBuffer226.value _ chunks n h

theorem installed_value (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install226V3.Types base))
    (chunks : PV_B3P_ByteOutput226.Chunks) (n : Usize)
    (h : PV_B3P_226V3.reference226.public_bytes
      (PV_B3P_PublicCarrier226V3.toSource base p) = .ok (.Ok (chunks,n))) :
    ∃ out : alloc.vec.Vec U8,
      @ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
        (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out) ∧
      out.val = PV_B3P_ByteLayout226V3.layout
        (PV_B3P_ProjectV3Law226.value (PV_B3P_PublicCarrier226V3.toSource base p)) := by
  refine ⟨PV_B3P_ByteOutput226.bytes chunks n,?_,reference_value _ chunks n h⟩
  rw [PV_B3P_Install226V3.source,h]
  rfl

#print axioms reference_value
#print axioms installed_value
end
end PV_B3P_InstalledBuffer226
