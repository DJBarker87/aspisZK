import R1DuplexRewind

/-! Read-order facts for an advanced state path in the execution trace. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexOrder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem advance_before (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State) (n : Nat)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < n, Read tr (advanceA p (s j))) :
    ∀ i j, i < j → j < n → Before tr (advanceA p (s i)) (advanceA p (s j)) := by
  have hadj (k : Nat) (hk : k + 1 < n) :
      Before tr (advanceA p (s k)) (advanceA p (s (k + 1))) := by
    apply noColl_prefix_after p Qtot H tr hcons hQ hcoll
      (advanceA p (s k)) (advanceA p (s (k + 1)))
      (hread k (by omega)) (hread (k + 1) hk)
    rw [toBytes_advanceA, hstep k (by omega)]
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases heq : i = j
      · subst i
        exact hadj j (by omega)
      · have hij' : i < j := by omega
        exact before_trans tr (ih i hij' (by omega)) (hadj j (by omega))

theorem advanced_ne (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State) (n : Nat)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < n, Read tr (advanceA p (s j))) :
    ∀ i j, i < j → j < n → s (i + 1) ≠ s (j + 1) := by
  intro i j hij hj heq
  have hbefore := advance_before p H tr Qtot hcons hQ hcoll s n hstep hread i j hij hj
  have haddr := before_ne tr hbefore
  have houtputs := noColl_injective p Qtot H tr hcons hQ hcoll
    (advanceA p (s i)) (advanceA p (s j)) (hread i (by omega)) (hread j hj) haddr
  apply houtputs
  rw [← hstep i (by omega), ← hstep j hj]
  exact heq

#print axioms advance_before
#print axioms advanced_ne

end AspisR1.DuplexOrder
end
