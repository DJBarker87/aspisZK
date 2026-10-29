import PV_L2E_GammaTrace
import PV_L2E_DigitsTrace
set_option autoImplicit false
namespace PV_L2E_CanonicalDecode
open PV_L2D_DivisionBounds

inductive Event where
  | check (index : Nat) (rejected : Bool)
  | construct
  | unwrap (panic : Bool)
  deriving DecidableEq

/-- The source short-circuit limb guard is read from left to right. The
successful construction merely places these same words into nested fields. -/
def check : Nat → List Nat → Bool × List Event
  | _,[] => (true,[.construct])
  | i,x::xs => if x≥P then (false,[.check i true])
    else let tail := check (i+1) xs
         (tail.1,.check i false::tail.2)

def plan : Nat → Nat → List Event
  | _,0 => [.construct]
  | i,n+1 => .check i false::plan (i+1) n

def decode (xs : List Nat) : Option (List Nat) × List Event :=
  let c := check 0 xs
  (if c.1 then some xs else none,c.2 ++ [.unwrap (!c.1)])

theorem checks_pass (i : Nat) (xs : List Nat) (small : ∀ x∈xs,x<P) :
    check i xs=(true,plan i xs.length) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    have hx : ¬x≥P := by have := small x (by simp); omega
    simp only [check,if_neg hx,ih (i+1) (fun y hy => small y (by simp [hy])),
      plan,List.length_cons]

theorem no_panic (xs : List Nat) (small : ∀ x∈xs,x<P) :
    decode xs=(some xs,plan 0 xs.length ++ [.unwrap false]) := by
  simp only [decode,checks_pass 0 xs small,Bool.not_true,↓reduceIte]

theorem ordinary (n : Nat) (xs : List Nat) (small : ∀ x∈xs,x<B) :
    decode (PV_L2E_DigitsTrace.run n xs).digits=
      (some (PV_L2E_DigitsTrace.run n xs).digits,plan 0 n ++ [.unwrap false]) := by
  rw [no_panic _ (PV_L2E_DigitsTrace.bounds n xs small).2,
    PV_L2E_DigitsTrace.digit_count]

theorem gamma (q : Nat) (ds : List Nat) :
    decode (PV_L2E_GammaTrace.run q ds).digits=
      (some (PV_L2E_GammaTrace.run q ds).digits,plan 0 ds.length ++ [.unwrap false]) := by
  rw [no_panic _ (PV_L2E_GammaTrace.output_bounds q ds),PV_L2E_GammaTrace.output_length]

#print axioms checks_pass
#print axioms no_panic
#print axioms ordinary
#print axioms gamma
end PV_L2E_CanonicalDecode
