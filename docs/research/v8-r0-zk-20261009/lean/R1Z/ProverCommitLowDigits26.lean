import R1SamplerRepeatedPass
/-! Symbolic limb/digit composition. Source/control binding is supplied by
separate exact paired-cell and verified-stub Kani gates (P6); this module
proves fold/traversal induction and arithmetic meaning without reducing any
concrete multi-limb division. Lists are in most-significant-limb order. -/
set_option autoImplicit false
namespace R1Z.ProverCommitLowDigits26
open AspisR1.SamplerWord AspisR1.SamplerWordPass AspisR1.SamplerRepeatedPass

def limb (s : UInt64 × List UInt32) (w : UInt32) : UInt64 × List UInt32 :=
  let cell := machineStep s.1 w
  (UInt64.ofNat cell.2.toNat, s.2 ++ [cell.1])

/-- A fold preserves every quotient limb, with an arbitrary already-written
written. This is the loop invariant, not an assumed pass correspondence. -/
theorem limbs (ws written : List UInt32) (r : UInt64) :
    ws.foldl limb (r,written) =
      ((machineProcess r ws).1,written ++ (machineProcess r ws).2) := by
  induction ws generalizing r written with
  | nil => simp only [List.foldl_nil,machineProcess,List.append_nil]
  | cons w ws ih =>
    simp only [List.foldl_cons,limb,machineProcess]
    rw [ih]
    simp only [List.append_assoc,List.singleton_append]

def iteratorPass (ws : List UInt32) : UInt64 × List UInt32 :=
  ws.foldl limb (0,[])

theorem pass (ws : List UInt32) : iteratorPass ws = machineProcess 0 ws := by
  rw [iteratorPass,limbs]
  simp only [List.nil_append]

def iteratorRun : Nat → List UInt32 → List Nat × List UInt32
  | 0, ws => ([],ws)
  | n+1, ws =>
    let step := iteratorPass ws
    let tail := iteratorRun n step.2
    (step.1.toNat :: tail.1,tail.2)

/-- All digits and the entire retained quotient agree, for every length. -/
theorem digits (n : Nat) (ws : List UInt32) : iteratorRun n ws = run n ws := by
  induction n generalizing ws with
  | zero => rfl
  | succ n ih => simp only [iteratorRun,run,pass,ih]

theorem low_digits (n : Nat) (ws : List UInt32) :
    (iteratorRun n ws).1 = AspisR1.SamplerNatModel.lowDigits
      AspisR1.SamplerMachineBounds.P n (wordValue ws) := by
  rw [digits,run_digits]

theorem remaining (n : Nat) (ws : List UInt32) :
    wordValue (iteratorRun n ws).2 = wordValue ws / AspisR1.SamplerMachineBounds.P^n := by
  rw [digits,run_remaining]

theorem canonical (n : Nat) (ws : List UInt32) :
    ∀ d ∈ (iteratorRun n ws).1, d < AspisR1.SamplerMachineBounds.P := by
  rw [digits]
  exact run_digits_canonical n ws

#print axioms limbs
#print axioms pass
#print axioms digits
#print axioms low_digits
#print axioms remaining
#print axioms canonical
end R1Z.ProverCommitLowDigits26
