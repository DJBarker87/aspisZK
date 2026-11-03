import PV_B3P_DominatedEvents578227
namespace PV_B3P_RangeEvents578227
open Aeneas Aeneas.Std core.ops.range PV_B3P_PanicPatterns571227
open PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- The source mutation affects start only; end is the private constructor
field. This is also a state-restoration law for the emitted Range next pair. -/
theorem next_end (handler : Str → Result Never) (r next : Range Usize) (item : Option Usize)
    (ran : PV_B3P_NextFormatting569227.source handler r = .ok (item,next)) :
    next.end = r.end := by
  by_cases active : r.start.val < r.end.val
  · simp only [PV_B3P_NextFormatting569227.source,if_pos active,
      PV_B3P_NthFormattingFinal559227.increment_value handler r.start r.end active,bind_tc_ok] at ran
    cases ran
    rfl
  · simp only [PV_B3P_NextFormatting569227.source,if_neg active] at ran
    cases ran
    rfl

theorem next_bound (handler : Str → Result Never) (r next : Range Usize) (item : Usize)
    (ran : PV_B3P_NextFormatting569227.source handler r = .ok (some item,next)) :
    item.val < r.end.val := by
  by_cases active : r.start.val < r.end.val
  · simp only [PV_B3P_NextFormatting569227.source,if_pos active,
      PV_B3P_NthFormattingFinal559227.increment_value handler r.start r.end active,bind_tc_ok] at ran
    cases ran
    exact active
  · simp only [PV_B3P_NextFormatting569227.source,if_neg active] at ran
    cases ran

/-- Finite successful source next edges interspersed with private-frame
stutters. Each actual loop entry is a zero/literal-end Range constructor. -/
def Edge (handler : Str → Result Never) (r next : Range Usize) : Prop :=
  r = next ∨ ∃ item, PV_B3P_NextFormatting569227.source handler r = .ok (item,next)

theorem private_end_invariant (handler : Str → Result Never) (finish : Usize) (r : Range Usize)
    (reached : Reachable (fun initial : Range Usize => initial.end = finish) (Edge handler) r) :
    r.end = finish := by
  induction reached with
  | initial h => exact h
  | next _ edge ih =>
    rcases edge with equal | ⟨item,ran⟩
    · exact equal ▸ ih
    · exact (next_end handler _ _ item ran).trans ih

/-- Prefix observation retains an arbitrary intervening Result computation
without deriving reachability from whole-function success. -/
def sourceEvent (handler : Str → Result Never) (r : Range Usize) (slack : Nat)
    (effects : List (Result Unit)) : Result (Option IndexState) := do
  let (item,_) ← PV_B3P_NextFormatting569227.source handler r
  match item with
  | none => .ok none
  | some i => through effects (some ⟨i.val,r.end.val+slack⟩)

theorem event_guard (handler : Str → Result Never) (r : Range Usize) (slack : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent handler r slack effects = .ok (some observed)) : indexGuard observed := by
  by_cases active : r.start.val < r.end.val
  · simp only [sourceEvent,PV_B3P_NextFormatting569227.source,if_pos active,
      PV_B3P_NthFormattingFinal559227.increment_value handler r.start r.end active,bind_tc_ok] at ran
    have frame := through_value _ _ _ ran
    cases frame
    change r.start.val < r.end.val + slack
    omega
  · simp only [sourceEvent,PV_B3P_NextFormatting569227.source,if_neg active,bind_tc_ok] at ran
    cases ran

theorem event_certificate {α : Type} (handler : Str → Result Never) (r : Range Usize) (slack : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent handler r slack effects = .ok (some observed)) (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second :=
  (index_out_of_bounds observed normal first second).2 (event_guard handler r slack effects observed ran)
#print axioms next_end
#print axioms next_bound
#print axioms private_end_invariant
#print axioms event_guard
#print axioms event_certificate
end PV_B3P_RangeEvents578227
