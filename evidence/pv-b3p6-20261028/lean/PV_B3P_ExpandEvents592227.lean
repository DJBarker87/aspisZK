import PV_B3P_CountdownEvents592227
import PV_B3P_ExpandSuccess227
namespace PV_B3P_ExpandEvents592227
open Aeneas Aeneas.Std PV_B3P_PanicPatterns571227 PV_B3P_InitializerEvents578227
set_option autoImplicit false
/-- Number of completed outer iterations; exhausted iterations stutter. -/
def depth (count n : Nat) : Nat := min n count

theorem depth_step (count n : Nat) :
    depth count (n+1) = if depth count n < count then depth count n+1 else depth count n := by
  simp only [depth]
  omega

/-- This closed form has exactly the source width update on every continuing
outer edge. Bounds here are local generic inputs, discharged at the two callers. -/
theorem width_step (count n capacity : Nat) (cap : 2^count ≤ capacity)
    (active : depth count n < count) :
    2 * 2^(depth count n) ≤ capacity := by
  have power := @Nat.pow_le_pow_right 2 (by omega) (depth count n+1) count (by omega)
  rw [Nat.pow_succ] at power
  omega

inductive Site where
  | point | parent | left | right

/-- Scalar source event: outer comparison, inner positive-test/decrement,
then the actual modular multiply/add. It exposes no bounds as hypotheses. -/
def sourceEvent (site : Site) (start count capacity outer inner : Nat)
    (effects : List (Result Unit)) : Result (Option IndexState) :=
  let d := depth count outer
  if start+d < start+count then
    if start+count ≤ 10 ∧ 2^count ≤ capacity then
      let width := 2^d
      let parent := width-inner-1
      if (match site with | .point => true | _ => false) then through effects (some ⟨start+d,10⟩)
      else if inner < width then
        let index := match site with
          | .point => start+d
          | .parent => parent
          | .left => (2*parent) % UScalar.size .Usize
          | .right => ((2*parent) % UScalar.size .Usize+1) % UScalar.size .Usize
        through effects (some ⟨index,capacity⟩)
      else .ok none
    else .ok none
  else .ok none

theorem event_certificate {α : Type} (site : Site) (start count capacity outer inner : Nat)
    (effects : List (Result Unit)) (observed : IndexState)
    (ran : sourceEvent site start count capacity outer inner effects = .ok (some observed))
    (normal first second : Result α) :
    ¬ diagnostic (indexGuard observed) ∧
      branch (indexGuard observed) normal first = branch (indexGuard observed) normal second := by
  apply (index_out_of_bounds observed normal first second).2
  simp only [sourceEvent] at ran
  split at ran
  · rename_i active
    split at ran
    · rename_i domain
      have dsmall : depth count outer < count := by omega
      have cap := width_step count outer capacity domain.2 dsmall
      have positive : 0 < 2^(depth count outer) := Nat.two_pow_pos _
      cases site with
      | point =>
        simp only at ran
        have frame := through_value _ _ _ ran
        cases frame
        change start+depth count outer < 10
        omega
      | parent =>
        simp only at ran
        split at ran
        · have frame := through_value _ _ _ ran
          cases frame
          change 2^(depth count outer)-inner-1 < capacity
          omega
        · cases ran
      | left =>
        simp only at ran
        split at ran
        · have frame := through_value _ _ _ ran
          cases frame
          change (2*(2^(depth count outer)-inner-1)) % UScalar.size .Usize < capacity
          have reduced := Nat.mod_le (2*(2^(depth count outer)-inner-1)) (UScalar.size .Usize)
          omega
        · cases ran
      | right =>
        simp only at ran
        split at ran
        · have frame := through_value _ _ _ ran
          cases frame
          change ((2*(2^(depth count outer)-inner-1)) % UScalar.size .Usize+1) % UScalar.size .Usize < capacity
          have first := Nat.mod_le (2*(2^(depth count outer)-inner-1)) (UScalar.size .Usize)
          have second := Nat.mod_le ((2*(2^(depth count outer)-inner-1)) % UScalar.size .Usize+1) (UScalar.size .Usize)
          omega
        · cases ran
    · cases ran
  · cases ran
#print axioms depth_step
#print axioms width_step
#print axioms event_certificate
end PV_B3P_ExpandEvents592227
