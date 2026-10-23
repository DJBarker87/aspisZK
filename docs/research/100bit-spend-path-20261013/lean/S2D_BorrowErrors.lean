import S2TrustedSdkBorrow

/-! Exact consequences of the ADOPTED fifteen-field trust item, not SDK
certification. Native E and original inputs remain fixed across every cut.
Relatedness, validity, enabledness and cut identity are explicit premises. -/
set_option autoImplicit false
namespace AspisR1.S2D
open AspisR1.S2Trust

/-- An admitted SDK cut from one execution. The native cut reader must be
instantiated by the lead; this structure cannot manufacture native execution. -/
structure BorrowCut {Native Input W F : Type} (E : Native) (original : Input)
    (L : Library W F) (nativeCut : Native → Nat → W) (index : Nat) where
  state : Heap F
  related : L.related (nativeCut E index) state
  valid : Valid state

variable {Native Input W F : Type} {E : Native} {original : Input}
variable {L : Library W F} {nativeCut : Native → Nat → W} {index : Nat}

theorem shared_failure (trust : S2TrustedSdkBorrow L)
    (c : BorrowCut E original L nativeCut index) (a t o : Nat)
    (enabled : Enabled c.state (.shared a t o))
    (conflict : c.state.counter (c.state.accounts a).1 < 0 ∨
      c.state.counter (c.state.accounts a).1 = maxCounter) :
    Matches L (nativeCut E index) (.shared a t o) (c.state, .borrowFailed) :=
  trust.shared_err _ _ a t o c.related c.valid enabled conflict

theorem exclusive_failure (trust : S2TrustedSdkBorrow L)
    (c : BorrowCut E original L nativeCut index) (a t o : Nat)
    (enabled : Enabled c.state (.exclusive a t o))
    (conflict : c.state.counter (c.state.accounts a).1 ≠ 0) :
    Matches L (nativeCut E index) (.exclusive a t o) (c.state, .borrowFailed) :=
  trust.exclusive_err _ _ a t o c.related c.valid enabled conflict

/-- Valid counters exhaust the shared-borrow success/error cases, including
saturation. No acceptance or initially-zero counter premise is used. -/
theorem shared_total_cases (trust : S2TrustedSdkBorrow L)
    (c : BorrowCut E original L nativeCut index) (a t o : Nat)
    (enabled : Enabled c.state (.shared a t o)) :
    (0 ≤ c.state.counter (c.state.accounts a).1 ∧
      c.state.counter (c.state.accounts a).1 < maxCounter ∧
      Matches L (nativeCut E index) (.shared a t o)
        (acquire c.state (c.state.accounts a).1 t o .shared, .guard t)) ∨
    ((c.state.counter (c.state.accounts a).1 < 0 ∨
      c.state.counter (c.state.accounts a).1 = maxCounter) ∧
      Matches L (nativeCut E index) (.shared a t o) (c.state, .borrowFailed)) := by
  by_cases hn : 0 ≤ c.state.counter (c.state.accounts a).1
  · by_cases hm : c.state.counter (c.state.accounts a).1 < maxCounter
    · exact Or.inl ⟨hn, hm, trust.shared_ok _ _ a t o c.related c.valid enabled hn hm⟩
    · have upper := (c.valid.2.1 (c.state.accounts a).1).2.1
      have eq : c.state.counter (c.state.accounts a).1 = maxCounter := by omega
      exact Or.inr ⟨Or.inr eq, shared_failure trust c a t o enabled (Or.inr eq)⟩
  · have neg : c.state.counter (c.state.accounts a).1 < 0 := by omega
    exact Or.inr ⟨Or.inl neg, shared_failure trust c a t o enabled (Or.inl neg)⟩

theorem exclusive_total_cases (trust : S2TrustedSdkBorrow L)
    (c : BorrowCut E original L nativeCut index) (a t o : Nat)
    (enabled : Enabled c.state (.exclusive a t o)) :
    (c.state.counter (c.state.accounts a).1 = 0 ∧
      Matches L (nativeCut E index) (.exclusive a t o)
        (acquire c.state (c.state.accounts a).1 t o .exclusive, .guard t)) ∨
    (c.state.counter (c.state.accounts a).1 ≠ 0 ∧
      Matches L (nativeCut E index) (.exclusive a t o) (c.state, .borrowFailed)) := by
  by_cases hz : c.state.counter (c.state.accounts a).1 = 0
  · exact Or.inl ⟨hz, trust.exclusive_ok _ _ a t o c.related c.valid enabled hz⟩
  · exact Or.inr ⟨hz, exclusive_failure trust c a t o enabled hz⟩

/-- Failure creates no guard, and moving/dropping its Err preserves the heap.
This does NOT discharge drops of guards acquired earlier in the adapter. -/
theorem failed_result_move_drop (trust : S2TrustedSdkBorrow L)
    (c : BorrowCut E original L nativeCut index) :
    Matches L (nativeCut E index) .errorMoveDrop (c.state, .borrowFailed) :=
  trust.error_move_drop _ _ c.related c.valid

#print axioms shared_failure
#print axioms exclusive_failure
#print axioms shared_total_cases
#print axioms exclusive_total_cases
#print axioms failed_result_move_drop
end AspisR1.S2D
