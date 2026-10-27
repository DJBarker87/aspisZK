import R1Z.PV_CB3_Op258Equal
import R1Z.PV_CB3_PoleBoolean
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op258RowLaw
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
local instance : DecidableEq aspis_core.field.QM31 := Classical.decEq _
abbrev Pair := Array aspis_core.field.QM31 2#usize
abbrev Row := Array Pair 2#usize

def clearRow (active : Bool) (chi a b c d : aspis_core.field.QM31) : Bool :=
  !(active && (decide (chi=a) || decide (chi=b) || decide (chi=c) || decide (chi=d)))

theorem clearRow_iff (active : Bool) (chi a b c d : aspis_core.field.QM31) :
    clearRow active chi a b c d = true ↔
      (active = true → chi ≠ a ∧ chi ≠ b ∧ chi ≠ c ∧ chi ≠ d) := by
  simp only [clearRow,Bool.not_eq_true,Bool.and_eq_false_iff,Bool.or_eq_false_iff,
    decide_eq_false_iff_not]
  cases active <;> simp

/-- Every premise describes an input read. No output or canonical field premise. -/
theorem body (values : Slice Row) (masks : Array U16 64#usize)
    (chi a b c d : aspis_core.field.QM31) (row : Usize) (clear : Bool)
    (mask : U16) (r : Row) (left right : Pair)
    (hrow : row < Slice.len values)
    (hm : Array.index_usize masks (Usize.wrapping_shr row 4#u32) = ok mask)
    (hr : Slice.index_usize values row = ok r)
    (hl : Array.index_usize r 0#usize = ok left)
    (hri : Array.index_usize r 1#usize = ok right)
    (ha : Array.index_usize left 0#usize = ok a)
    (hb : Array.index_usize left 1#usize = ok b)
    (hc : Array.index_usize right 0#usize = ok c)
    (hd : Array.index_usize right 1#usize = ok d) :
    PV_CB3_Op258Ref.reference.all_slots_clear_loop.body values masks chi clear row =
      ok (cont (clear && clearRow
        ((mask &&& U16.wrapping_shl 1#u16 (UScalar.cast .U32 (row &&& 15#usize))) != 0#u16)
        chi a b c d,Usize.wrapping_add row 1#usize)) := by
  simp only [PV_CB3_Op258Ref.reference.all_slots_clear_loop.body,if_pos hrow,lift,
    bind_tc_ok,hm,hr,hl,hri,ha,hb,hc,hd,PV_CB3_Op258Equal.source]
  simp only [decide_not,Bool.decide_eq_true]
  change ok (cont (PV_CB3_PoleBoolean.row clear _ _ _ _ _,_)) = _
  rw [PV_CB3_PoleBoolean.row_value]
  rfl
#print axioms clearRow_iff
#print axioms body
end R1Z.PV_CB3_Op258RowLaw
