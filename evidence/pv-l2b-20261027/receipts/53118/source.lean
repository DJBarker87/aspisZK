import PV_L2B_Rejection

/-! Literal scalar control over supplied UInt32 words. The caller supplies at
least 16 words from the expander; assigning that stream its E2 law, cursor
state refinement, native effects and hash observations remain separate. -/
set_option autoImplicit false
namespace PV_L2B_SourceWords

def candidate (raw : UInt32) : Nat := (raw &&& 0x7fffffff).toNat

def classify (raw : UInt32) : Option Nat :=
  if candidate raw < 2147483647 then some (candidate raw) else none

def source : Nat → List UInt32 → Nat × Option Nat
  | 0, _ => (0, none)
  | _+1, [] => (0, none)
  | n+1, raw::rest =>
    let c := candidate raw
    if c < 2147483647 then (1, some c)
    else let result := source n rest; (result.1+1, result.2)

theorem source_scan (n : Nat) (words : List UInt32) :
    source n words = PV_L2B_Rejection.scan n (words.map classify) := by
  induction n generalizing words with
  | zero => rfl
  | succ n ih =>
    cases words with
    | nil => rfl
    | cons raw rest =>
      by_cases h : candidate raw < 2147483647
      · simp [source, classify, PV_L2B_Rejection.scan, h]
      · simp [source, classify, PV_L2B_Rejection.scan, h, ih]

theorem source_consumed_bound (n : Nat) (words : List UInt32) :
    (source n words).1 ≤ n := by
  rw [source_scan]
  exact PV_L2B_Rejection.consumed_le_cap n _

theorem source_count_relabel (transform : UInt32 → UInt32) (f : Nat → Nat)
    (preserves : ∀ w, classify (transform w) = (classify w).map f)
    (n : Nat) (words : List UInt32) :
    (source n (words.map transform)).1 = (source n words).1 := by
  rw [source_scan, source_scan]
  have h : (words.map transform).map classify = (words.map classify).map (Option.map f) := by
    induction words with
    | nil => rfl
    | cons w ws ih => simp only [List.map_cons, preserves w, ih]
  rw [h, PV_L2B_Rejection.count_map]

#print axioms source_scan
#print axioms source_consumed_bound
#print axioms source_count_relabel
end PV_L2B_SourceWords
