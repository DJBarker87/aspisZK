import LPf_DotResidueStep
set_option autoImplicit false
namespace AspisR1.LPm_WordFold
open Aeneas Aeneas.Std
abbrev bound := LPf_DotWordStep.bound

def run (sum : U64) : List U64 → U64
  | [] => sum
  | raw::xs => run (LPf_DotPushFour.update sum raw) xs

/-- Every reached count supplies the next native step's no-wrap invariant.
All raw representatives are included; no multiplication is evaluated here. -/
theorem bounded (xs : List U64) (sum : U64) (n : Nat)
    (fits : n+xs.length ≤ 4096) (hs : sum.val ≤ n*bound) :
    (run sum xs).val ≤ (n+xs.length)*bound := by
  induction xs generalizing sum n with
  | nil => simpa only [run,List.length_nil,Nat.add_zero] using hs
  | cons raw xs ih =>
    have hn : n<4096 := by simp only [List.length_cons] at fits; omega
    have update := (LPf_DotWordStep.value sum raw n hn hs).2
    have tail := ih (LPf_DotPushFour.update sum raw) (n+1)
      (by simp only [List.length_cons] at fits; omega) update
    simpa only [run,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

/-- Product-sum value invariant for an arbitrary source-shaped prefix, on
EVERY raw u64 sequence fitting the public count cap. -/
theorem residues (xs : List U64) (sum : U64) (n : Nat)
    (fits : n+xs.length ≤ 4096) (hs : sum.val ≤ n*bound) :
    (run sum xs).val%2147483647 =
      (sum.val+(xs.map UScalar.val).sum)%2147483647 := by
  induction xs generalizing sum n with
  | nil => simp only [run,List.map_nil,List.sum_nil,Nat.add_zero]
  | cons raw xs ih =>
    have hn : n<4096 := by simp only [List.length_cons] at fits; omega
    have update := (LPf_DotWordStep.value sum raw n hn hs).2
    have tail := ih (LPf_DotPushFour.update sum raw) (n+1)
      (by simp only [List.length_cons] at fits; omega) update
    rw [run,tail]
    rw [Nat.add_mod,LPf_DotResidueStep.source sum raw n hn hs,←Nat.add_mod]
    simp only [List.map_cons,List.sum_cons,Nat.add_assoc]

theorem twenty_nine (xs : List U64) (size : xs.length=29) :
    (run 0#u64 xs).val ≤ 29*bound ∧
    (run 0#u64 xs).val%2147483647 = (xs.map UScalar.val).sum%2147483647 := by
  constructor
  · simpa only [size,Nat.zero_add] using bounded xs 0#u64 0 (by omega) (by decide)
  · simpa only [show (0#u64).val=0 from rfl,Nat.zero_add] using
      residues xs 0#u64 0 (by omega) (by decide)

#print axioms bounded
#print axioms residues
#print axioms twenty_nine
end AspisR1.LPm_WordFold
