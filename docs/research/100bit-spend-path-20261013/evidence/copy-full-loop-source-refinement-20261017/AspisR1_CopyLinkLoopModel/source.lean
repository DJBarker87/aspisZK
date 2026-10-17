import CopyRegistryModel
import AspisR1.CopyLinkStepExact

/-! Symbolic suffix-fold equations for the fixed model registry. No literal
record, field value or source loop is unfolded by the traversal model. -/
set_option autoImplicit false
namespace AspisR1.CopyLinkLoopModel
noncomputable section
open AspisR1.CopyRegistryModel AspisR1.CopyLinkStepExact
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Row := R0P.CopyRowExtension ExactQM

def remaining (index : Nat) (variant : R0P.Variant)
    (patterns : Fin 14 → ExactQM) (selectors : R0P.CopySelectors ExactQM)
    (cursor : Nat) (row : Row) : Row :=
  (modelRegistry.drop cursor).foldl
    (fun acc link => modelStep acc link index variant patterns selectors) row

theorem remaining_end (index : Nat) (variant : R0P.Variant)
    (patterns : Fin 14 → ExactQM) (selectors : R0P.CopySelectors ExactQM) (row : Row) :
    remaining index variant patterns selectors 136 row = row := by
  unfold remaining
  rw [← modelRegistry_length, List.drop_length]
  rfl

theorem remaining_step (index : Nat) (variant : R0P.Variant)
    (patterns : Fin 14 → ExactQM) (selectors : R0P.CopySelectors ExactQM)
    (cursor : Fin 136) (row : Row) :
    remaining index variant patterns selectors cursor.val row =
      remaining index variant patterns selectors (cursor.val + 1)
        (modelStep row (modelAt cursor) index variant patterns selectors) := by
  unfold remaining
  have hi : cursor.val < modelRegistry.length := by
    rw [modelRegistry_length]
    exact cursor.isLt
  rw [List.drop_eq_getElem_cons hi, modelRegistry_getElem cursor]
  rfl

theorem remaining_zero (index : Nat) (variant : R0P.Variant)
    (patterns : Fin 14 → ExactQM) (selectors : R0P.CopySelectors ExactQM) (row : Row) :
    remaining index variant patterns selectors 0 row =
      R0P.copyLinks.foldl
        (fun acc link => modelStep acc link index variant patterns selectors) row := by
  unfold remaining
  rw [List.drop_zero, model_registry_exact]

#print axioms remaining_end
#print axioms remaining_step
#print axioms remaining_zero
end
end AspisR1.CopyLinkLoopModel
