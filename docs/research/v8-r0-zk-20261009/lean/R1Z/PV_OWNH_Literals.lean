import R1Z.PV_OWNH_Address
import R1Z.PV_RDB2D_MasksWorld
set_option autoImplicit false
namespace R1Z.PV_OWNH_Literals
open Aeneas Aeneas.Std Result ProverRwFull

/-- Explicit 214-word literal is the `expected` definition in
PV_RDB2D_PV_B3P_Sorted133.lean. No sort is evaluated to obtain this literal. -/
abbrev rowsLiteral : List Nat := PV_B3P_Sorted133.expected
/-- Explicit 64-word literal is `after` in PV_RDB2D_MaskChunk13.lean.
The 14 named chunk laws establish it from the original 214 rows. -/
abbrev masksLiteral : PV_RDB2D_MasksLoop.Masks := PV_RDB2D_MaskChunk13.after

theorem v229_result : PV_B3P_SortedResult133.active = .ok rowsLiteral :=
  PV_B3P_SortedResult133.complete_result

theorem v229_selected (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op133 base (PV_B3P_Install133.selected base ops) =
      .ok (.Ok PV_B3P_Install133.value) := PV_B3P_Install133.source base ops

theorem v229_selected_values :
    PV_B3P_Install133.value.val.map (fun x => x.val) = rowsLiteral :=
  PV_B3P_Closure133.value_nat

def masksModel : Except PV_B3P_Schedule133.Error PV_RDB2D_MasksLoop.Masks :=
  match PV_B3P_SortedResult133.active with
  | .error e => .error e
  | .ok rows => .ok (PV_RDB2D_MasksLoop.run rows PV_RDB2D_MasksValue.initial)

theorem v230_result : masksModel = .ok masksLiteral := by
  unfold masksModel
  rw [v229_result]
  exact congrArg Except.ok PV_RDB2D_MasksValue.concrete

theorem row_length : rowsLiteral.length = 214 :=
  PV_B3P_SortedResult133.expected_length

theorem mask_length : masksLiteral.length = 64 := PV_RDB2D_MasksValue.length

/-- Public request layouts are independent of allocator-returned bases. -/
theorem request_layouts (address : Nat) :
    PV_RDB2D_CollectorTrace.publicRequest PV_RDB2D_CollectorRequests.first =
      .allocate 1016 2 ∧
    PV_RDB2D_CollectorTrace.publicRequest (PV_RDB2D_CollectorRequests.second address) =
      .reallocate 1016 2 2032 ∧
    PV_RDB2D_CollectorTrace.publicRequest PV_RDB2D_CollectorRequests.third =
      .allocate 544 2 :=
  ⟨PV_RDB2D_CollectorRequests.first_public,
   PV_RDB2D_CollectorRequests.second_public address,
   PV_RDB2D_CollectorRequests.third_public⟩

#print axioms v229_result
#print axioms v229_selected
#print axioms v229_selected_values
#print axioms v230_result
#print axioms row_length
#print axioms mask_length
#print axioms request_layouts
end R1Z.PV_OWNH_Literals
