import R1Z.PV_RDCD4_LazyComponents
import R1Z.PV_RDCD3_Index194
import R1Z.PV_RDCD3_ArrayWrite194
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyCell
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents
abbrev Sums := List (List U64)
abbrev read := @PV_RDCD3_Index194.read
/-- RHS factors are read before the destination place. Both changed nested
arrays are returned, including the outer writeback. Release wrapping integer effects
retain failure and divergence; no arithmetic callback has been introduced. -/
def cell (left right : List (List M)) (sums : Sums) (row col : Nat) : Result Sums := do
  let lrow ← read left row
  let l ← read lrow col
  let rrow ← read right row
  let r ← read rrow col
  let l ← lift (UScalar.cast .U64 l)
  let r ← lift (UScalar.cast .U64 r)
  let product := U64.wrapping_mul l r
  let oldrow ← read sums row
  let old ← read oldrow col
  let value := U64.wrapping_add old product
  let newrow ← PV_RDCD3_ArrayWrite194.write oldrow col value
  PV_RDCD3_ArrayWrite194.write sums row newrow

theorem changed_outer (sums : Sums) (row col : Nat) (value : U64)
    (r : List U64) (hr : read sums row = ok r) (hc : col < r.length)
    (bound : row < sums.length) :
    (do let r ← read sums row
        let r ← PV_RDCD3_ArrayWrite194.write r col value
        PV_RDCD3_ArrayWrite194.write sums row r) =
      ok (sums.set row (r.set col value)) := by
  rw [hr,bind_tc_ok,PV_RDCD3_ArrayWrite194.success r col value hc,bind_tc_ok,
    PV_RDCD3_ArrayWrite194.success sums row (r.set col value) bound]
#print axioms changed_outer
end R1Z.PV_RDCD4_LazyCell
