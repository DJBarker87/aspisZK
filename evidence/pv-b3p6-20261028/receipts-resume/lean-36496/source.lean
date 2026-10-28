import PV_B3P_Install226V3
import PV_B3P_ChunkFlatten226
namespace PV_B3P_SerializerBridge226
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section

-- A conditional bridge naming the remaining value obligation explicitly.
-- It is not a row closure and does not introduce a trust item.
theorem installed_value_of_cells (base : ExternalTypes)
    (ops : @ExternalFuns (PV_B3P_Install226V3.Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
      (PV_B3P_Install226V3.Types base))
    (chunks : PV_B3P_ByteOutput226.Chunks) (n : Usize) (layout : List U8)
    (hr : PV_B3P_226V3.reference226.public_bytes
      (PV_B3P_PublicCarrier226V3.toSource base p) = .ok (.Ok (chunks,n)))
    (hn : n.val = layout.length) (hb : layout.length ≤ 1472)
    (cells : ∀ i, i < layout.length →
      (PV_B3P_ByteOutput226.flatten chunks)[i]? = layout[i]?) :
    ∃ out : alloc.vec.Vec U8,
      @ExternalFuns.op226 (PV_B3P_Install226V3.Types base)
        (PV_B3P_Install226V3.selected base ops) p = .ok (.Ok out) ∧ out.val = layout := by
  refine ⟨PV_B3P_ByteOutput226.bytes chunks n,?_,?_⟩
  · rw [PV_B3P_Install226V3.source,hr]
    rfl
  · exact PV_B3P_ChunkFlatten226.take_value chunks n layout hn hb cells

#print axioms installed_value_of_cells
end
end PV_B3P_SerializerBridge226
