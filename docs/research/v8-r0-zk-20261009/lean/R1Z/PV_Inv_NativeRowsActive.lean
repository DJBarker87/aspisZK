import R1Z.PV_Inv_RegistryInput
import R1Z.PV_Inv_MaskSource
set_option autoImplicit false
namespace R1Z.PV_Inv_NativeRowsActive
open R0P PV_Inv_RegistryInput
variable {K : Type} [Field K]

def rows (registry : List (SourceLink K)) : List (Fin 1024) :=
  registry.flatMap (fun link => [link.producer.row,link.consumer.row])

theorem member (registry : List (SourceLink K)) (enumeration : P_registry registry)
    (row : Fin 1024) (hr : row ∈ rows registry) : CopyActiveRow row := by
  have eqn : rows registry = PV_Inv_MaskSource.rows := by
    rw [rows,enumeration,List.flatMap_map]
    rfl
  rw [eqn] at hr
  exact PV_Inv_MaskSource.rows_active row hr

#print axioms member
end R1Z.PV_Inv_NativeRowsActive
