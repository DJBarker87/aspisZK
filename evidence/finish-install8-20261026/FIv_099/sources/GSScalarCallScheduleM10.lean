import CompPolyFactorRawDivisionBridge
import GSBinaryModPowerWorkM10

/-! Occurrence trace for the maintained trial/retry/factor scheduler. The
trace includes failures and skips the right subtree after a left abort.
It records actual operands; it is not yet the complete RR/interpolation
Resources ledger. Power calls name the actual binaryRec backend. -/
set_option autoImplicit false
namespace AspisR1.GSScalarCallScheduleM10
open CompPoly CompPolySplitTrial CompPolySplitRetries CompPolyFactorRecursion
variable {K : Type} [Field K] [BEq K] [LawfulBEq K]

inductive Call (K : Type) [Field K] [BEq K] [LawfulBEq K] where
  | gcd (p q : CPolynomial K)
  | power (a m : CPolynomial K) (e : Nat)
  | division (p q : CPolynomial K)

def trial (f h : CPolynomial K) (q : Nat) : Option (CPolynomial K) × List (Call K) :=
  let d0 := CPolynomial.gcdMonic f h
  if proper d0 f then (some d0, [.gcd f h]) else
    let a := CompPolyPolynomialBackendBridge.modPower h f (q/2)
    let d1 := CPolynomial.gcdMonic f (a-1)
    (if proper d1 f then some d1 else none,
      [.gcd f h, .power h f (q/2), .gcd f (a-1)])

theorem trial_value (f h : CPolynomial K) (q : Nat) : (trial f h q).1 = trySplit f h q := by
  unfold trial trySplit
  dsimp only
  split <;> rfl

theorem trial_length (f h : CPolynomial K) (q : Nat) : (trial f h q).2.length ≤ 3 := by
  unfold trial
  dsimp only
  split
  · change 1 ≤ 3; omega
  · change 3 ≤ 3; omega

def retry (f : CPolynomial K) (q : Nat) :
    (t : Nat) → (Fin t → K × K) → Option (CPolynomial K) × List (Call K)
  | 0, _ => (none, [])
  | t+1, tape =>
    let r := trial f (linear (tape 0)) q
    match r.1 with
    | some d => (some d, r.2)
    | none => let tail := retry f q t (fun i => tape i.succ)
              (tail.1, r.2++tail.2)

theorem retry_value (f : CPolynomial K) (q t : Nat) (tape : Fin t → K × K) :
    (retry f q t tape).1 = CompPolySplitRetries.retry f q t tape := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [retry, CompPolySplitRetries.retry, trial_value]
    cases trySplit f (linear (tape 0)) q with
    | none => exact ih _
    | some d => rfl

theorem retry_length (f : CPolynomial K) (q t : Nat) (tape : Fin t → K × K) :
    (retry f q t tape).2.length ≤ 3*t := by
  induction t with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    have hh := trial_length f (linear (tape 0)) q
    have ht := ih (fun i => tape i.succ)
    simp only [retry]
    split
    · change (trial f (linear (tape 0)) q).2.length ≤ 3*(t+1)
      omega
    · change ((trial f (linear (tape 0)) q).2 ++
        (retry f q t (fun i => tape i.succ)).2).length ≤ 3*(t+1)
      rw [List.length_append]
      omega

def factor (q t : Nat) (coins : Nat → Fin t → K × K) :
    Nat → Nat → CPolynomial K → Option (List K) × List (Call K)
  | 0, _, _ => (none, [])
  | fuel+1, node, f =>
    if f.natDegree = 0 then (some [], []) else
    if f.natDegree = 1 then (some [-f.coeff 0], []) else
    let r := retry f q t (coins node)
    match r.1 with
    | none => (none, r.2)
    | some d =>
      let left := factor q t coins fuel (2*node+1) d
      match left.1 with
      | none => (none, r.2++left.2)
      | some l =>
        let right := factor q t coins fuel (2*node+2) (f.divByMonic d)
        (right.1.map (fun rs => l++rs), r.2++left.2++[.division f d]++right.2)

theorem factor_value (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) :
    (factor q t coins fuel node f).1 = CompPolyFactorRecursion.factor q t coins fuel node f := by
  induction fuel generalizing node f with
  | zero => rfl
  | succ fuel ih =>
    simp only [factor, CompPolyFactorRecursion.factor, retry_value]
    split
    · rfl
    · split
      · rfl
      · cases CompPolySplitRetries.retry f q t (coins node) with
        | none => rfl
        | some d =>
          dsimp only
          rw [ih]
          cases CompPolyFactorRecursion.factor q t coins fuel (2*node+1) d with
          | none => rfl
          | some l =>
            dsimp only
            rw [ih]
            cases CompPolyFactorRecursion.factor q t coins fuel (2*node+2) (f.divByMonic d) <;> rfl

def fuelBudget (t : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => 3*t+2*fuelBudget t n+1

theorem factor_length (q t : Nat) (coins : Nat → Fin t → K × K)
    (fuel node : Nat) (f : CPolynomial K) :
    (factor q t coins fuel node f).2.length ≤ fuelBudget t fuel := by
  induction fuel generalizing node f with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    have hr := retry_length f q t (coins node)
    simp only [factor, fuelBudget]
    split
    · simp only [List.length_nil]; omega
    · split
      · simp only [List.length_nil]; omega
      · split
        · dsimp only; omega
        · rename_i d hd
          have hl := ih (2*node+1) d
          have hh := ih (2*node+2) (f.divByMonic d)
          split <;> dsimp only <;>
            simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

#print axioms trial_value
#print axioms trial_length
#print axioms retry_value
#print axioms retry_length
#print axioms factor_value
#print axioms factor_length
end AspisR1.GSScalarCallScheduleM10
