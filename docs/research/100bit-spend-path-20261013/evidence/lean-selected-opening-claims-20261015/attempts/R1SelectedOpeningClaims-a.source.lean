import R1CircleRecordCodec
import R1OpeningRecordCodec
import R1JointFunctionalBinding

/-! A typed model interface for the six 29-entry vectors used by the selected
opening binding layer. This only packages provided payloads; it proves no
source correspondence, commitment recovery, or acceptance fact. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedOpeningClaims

open scoped BigOperators
open AspisR1.CircleRecordCodec AspisR1.OpeningRecordCodec

abbrev E := AspisWideTower.WideExact
abbrev LowWide := AspisR1.SemanticCoefficientCodec.LowWide

/-- Six vectors in the selected order: three row-25 claims, row-25 extra,
row-26 before-Z1, and row-27 gamma payload. -/
def Y (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma) :
    Fin 6 → Fin 29 → E := fun j l =>
  match j.val with
  | 0 => (CircleRecordCodec.pointClaims row25 ⟨0, by omega⟩ l).val
  | 1 => (CircleRecordCodec.pointClaims row25 ⟨1, by omega⟩ l).val
  | 2 => (CircleRecordCodec.pointClaims row25 ⟨2, by omega⟩ l).val
  | 3 => (CircleRecordCodec.extra row25 l).val
  | 4 => (CircleRecordCodec.beforeZ1 row26 l).val
  | 5 => (row27 l).val
  | _ => False.elim (by omega)

def parts (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (c0 gamma : E) : Fin 7 → E :=
  Fin.cases c0 (fun j =>
    ∑ l : Fin 29, gamma ^ l.val * Y row25 row26 row27 j l)

theorem Y_point (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (j : Fin 3) (l : Fin 29) :
    Y row25 row26 row27 ⟨j.val, by omega⟩ l =
      (CircleRecordCodec.pointClaims row25 j l).val := by
  fin_cases j <;> rfl

theorem Y_extra (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (l : Fin 29) :
    Y row25 row26 row27 ⟨3, by omega⟩ l =
      (CircleRecordCodec.extra row25 l).val := rfl

theorem Y_beforeZ1 (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (l : Fin 29) :
    Y row25 row26 row27 ⟨4, by omega⟩ l =
      (CircleRecordCodec.beforeZ1 row26 l).val := rfl

theorem Y_gamma (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (l : Fin 29) :
    Y row25 row26 row27 ⟨5, by omega⟩ l = (row27 l).val := rfl

theorem Y_im_zero (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (j : Fin 6) (l : Fin 29) : (Y row25 row26 row27 j l).im = 0 := by
  fin_cases j <;> simp [Y, CircleRecordCodec.pointClaims,
    CircleRecordCodec.extra, CircleRecordCodec.beforeZ1,
    SemanticCoefficientCodec.LowWide]

theorem parts_weighted_sum (row25 : CircleRecordCodec.Payload 0)
    (row26 : CircleRecordCodec.Payload 1)
    (row27 : OpeningRecordCodec.Payload .gamma)
    (c0 gamma kappa : E) :
    (∑ j : Fin 7, kappa ^ j.val * parts row25 row26 row27 c0 gamma j) =
      JointFunctionalBinding.claimedValue (Y row25 row26 row27) c0 gamma kappa := by
  simp [parts, JointFunctionalBinding.claimedValue, Fin.sum_univ_succ]

#print axioms Y_point
#print axioms Y_extra
#print axioms Y_beforeZ1
#print axioms Y_gamma
#print axioms Y_im_zero
#print axioms parts_weighted_sum

end AspisR1.SelectedOpeningClaims
end
