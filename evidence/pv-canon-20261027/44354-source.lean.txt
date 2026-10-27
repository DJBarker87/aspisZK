import R1Z.PV_Canon_RoundCounter
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std
/-- Pure control relation: entry at zero, successful continuation adds one,
and round ten terminates. Association with the extracted recursive Result
body is still required; this relation is not asserted as a native trace. -/
inductive RoundVisit : Usize → Prop
  | initial : RoundVisit 0#usize
  | next {round : Usize} : RoundVisit round → round≠10#usize →
      RoundVisit (Usize.wrapping_add round 1#usize)
 theorem visited_round_le {round : Usize} (visit : RoundVisit round) : round.val ≤ 10 := by
  induction visit with
  | initial => change 0 ≤ 10; omega
  | @next round visit ne ih =>
    have hlt : round.val < 10 := by
      have hn : round.val ≠ 10 := fun h => ne (UScalar.eq_of_val_eq h)
      omega
    rw [next_round_val round hlt]
    omega
 theorem evaluated_round_lt {round : Usize} (visit : RoundVisit round) (guard : round≠10#usize) :
    round.val < 10 := by
  have hle := visited_round_le visit
  have hn : round.val≠10 := fun h => guard (UScalar.eq_of_val_eq h)
  omega
#print axioms visited_round_le
#print axioms evaluated_round_lt
end R1Z.PV_Canon
