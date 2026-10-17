import PoseidonInternalStateWords

/-! A symbolic sum for any number of source coordinates. No concrete lane
recurrence is evaluated by this correspondence. -/
set_option autoImplicit false
namespace AspisR1.PoseidonInternalRemainingSum
open AspisR1.PoseidonFullRoundCellStep (State)
open AspisR1.PoseidonInternalStateWords

theorem remaining_eq_sum (state : State) (start fuel : Nat) (limb : Fin 4) :
    remaining state start fuel limb =
      (List.ofFn (fun i : Fin fuel => wordNat state (start+i.val) limb)).sum := by
  induction fuel generalizing start with
  | zero => simp only [remaining,List.ofFn_zero,List.sum_nil]
  | succ fuel ih =>
    rw [remaining,List.ofFn_succ,List.sum_cons,ih]
    have htail : (fun i : Fin fuel => wordNat state (start+1+i.val) limb) =
        (fun i : Fin fuel => wordNat state (start+i.succ.val) limb) := by
      funext i
      have hi : start+1+i.val = start+i.succ.val := by
        change start+1+i.val = start+(i.val+1)
        omega
      rw [hi]
    simpa only [Fin.val_zero,Nat.add_zero,htail]

#print axioms remaining_eq_sum
end AspisR1.PoseidonInternalRemainingSum
