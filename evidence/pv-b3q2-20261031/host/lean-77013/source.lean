import PV_B3Q_TableGuards
namespace PV_B3Q_FormattingBranches
open PV_B3Q_FrozenTables PV_B3Q_PanicGuards
set_option autoImplicit false
/-- A source branch with an arbitrary formatting continuation. Replacing the
continuation on the excluded branch does not require any formatter model. -/
def checked {α : Type} (safe : Bool) (value : α) (panicFormat : Unit → α) : α :=
 if safe then value else panicFormat ()
theorem checked_unreachable {α : Type} (value : α) (panicFormat : Unit → α) :
 checked true value panicFormat = value := rfl
/-- Source link_weight's five exact match arms; the caller supplies each arm's
arithmetic result. The default arm represents panic argument construction. -/
def weight_dispatch {α : Type} (kind : Nat) (one transfer withdrawal left right : α)
    (panicFormat : Unit → α) : α :=
 match kind with
 | 0 => one | 1 => transfer | 2 => withdrawal | 3 => left | 4 => right
 | _ => panicFormat ()
theorem weight_format_unreachable {α : Type} (kind : Nat) (guard : kind < 5)
    (one transfer withdrawal left right : α) (first second : Unit → α) :
 weight_dispatch kind one transfer withdrawal left right first =
 weight_dispatch kind one transfer withdrawal left right second := by
 interval_cases kind <;> rfl
/-- No input guard is added: every compiled link is an immutable table member. -/
theorem frozen_weight_format_unreachable {α : Type} (link : Link) (member : link ∈ links)
    (one transfer withdrawal left right : α) (first second : Unit → α) :
 weight_dispatch link.1 one transfer withdrawal left right first =
 weight_dispatch link.1 one transfer withdrawal left right second :=
 weight_format_unreachable link.1 (link_member_safe link member).1 one transfer withdrawal left right first second
/-- The two native dot calls map the SAME fixed row array. No writer semantics
or equality of the field values is needed to exclude assert_failed. -/
theorem dot_assert_format_unreachable {α β γ δ ε : Type} (rows : List α)
    (f : α → β) (g : α → γ) (h : α → δ) (value : ε) (panicFormat : Unit → ε) :
 checked (decide ((rows.map f).length = (rows.map g).length ∧
                 (rows.map f).length = (rows.map h).length)) value panicFormat = value := by
 simp only [List.length_map,decide_true,checked,if_true]
/-- Dynamic pattern-column bounds in the original source, not an inference
from optimized absence. Immutable table membership supplies the branch test. -/
theorem pattern_column_format_unreachable {α : Type} (column : Nat)
    (member : column ∈ columns) (value : α) (panicFormat : Unit → α) :
 checked (decide (column < 16)) value panicFormat = value := by
 have safe := column_member_bound column member
 simp only [checked,safe,decide_true,if_true]
/-- Copy endpoint read at high[row>>4], low[row&15]. -/
theorem endpoint_format_unreachable {α : Type} (link : Link) (member : link ∈ links)
    (value : α) (panicFormat : Unit → α) :
 checked (decide (link.2.2.1.1 / 16 < 64 ∧ link.2.2.1.1 % 16 < 16 ∧
    link.2.2.1.2.1 < 2 ∧ link.2.2.1.2.2 < 14 ∧
    link.2.2.2.1 / 16 < 64 ∧ link.2.2.2.1 % 16 < 16 ∧
    link.2.2.2.2.1 < 2 ∧ link.2.2.2.2.2 < 14)) value panicFormat = value := by
 have safe := link_member_safe link member
 have hp := endpoint_selector_bounds link.2.2.1.1 safe.2.2.1
 have hc := endpoint_selector_bounds link.2.2.2.1 safe.2.2.2.2.2.1
 have all : link.2.2.1.1 / 16 < 64 ∧ link.2.2.1.1 % 16 < 16 ∧
    link.2.2.1.2.1 < 2 ∧ link.2.2.1.2.2 < 14 ∧
    link.2.2.2.1 / 16 < 64 ∧ link.2.2.2.1 % 16 < 16 ∧
    link.2.2.2.2.1 < 2 ∧ link.2.2.2.2.2 < 14 := by omega
 simp only [checked,all,decide_true,if_true]
#print axioms checked_unreachable
#print axioms weight_format_unreachable
#print axioms frozen_weight_format_unreachable
#print axioms dot_assert_format_unreachable
#print axioms pattern_column_format_unreachable
#print axioms endpoint_format_unreachable
end PV_B3Q_FormattingBranches
