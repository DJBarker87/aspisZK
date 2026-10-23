import S2D_BorrowErrors

/-! Library drop side conditions follow from validity at the SAME native cut.
This is not a proof of compiler Drop order or validity preservation by children. -/
set_option autoImplicit false
namespace AspisR1.S2D
open AspisR1.S2Trust
variable {Native Input W F : Type} {E : Native} {original : Input}
variable {L : Library W F} {nativeCut : Native → Nat → W} {index : Nat}

theorem live_guard_count_positive (c : BorrowCut E original L nativeCut index)
    (t : Nat) (g : Guard) (live : lookup c.state t = some g) :
    0 < count c.state g.cell g.kind := by
  have mem : g ∈ c.state.guards := List.mem_of_find?_eq_some live
  have filtered : g ∈ c.state.guards.filter (fun h => h.cell == g.cell && h.kind == g.kind) := by
    exact List.mem_filter.mpr ⟨mem, by simp⟩
  have pos := List.length_pos_iff.mpr (List.ne_nil_of_mem filtered)
  change 0 < (((c.state.guards.filter (fun h => h.cell == g.cell && h.kind == g.kind)).length) : Int)
  omega

theorem shared_drop_counter_positive (c : BorrowCut E original L nativeCut index)
    (t : Nat) (g : Guard) (live : lookup c.state t = some g) (shared : g.kind = .shared) :
    0 < c.state.counter g.cell := by
  have pos := live_guard_count_positive c t g live
  rw [shared] at pos
  rcases c.valid.2.1 g.cell with ⟨_, _, balance, exclusive, external⟩
  have nonnegative : 0 ≤ c.state.external g.cell := by
    by_cases hn : c.state.external g.cell < 0
    · have hz := (external hn).1
      omega
    · omega
  have noExclusive : count c.state g.cell .exclusive = 0 := by
    have nn : 0 ≤ count c.state g.cell .exclusive := by unfold count; omega
    by_cases hp : 0 < count c.state g.cell .exclusive
    · have hz := (exclusive hp).2.1
      omega
    · omega
  omega

theorem exclusive_drop_counter_negative_one (c : BorrowCut E original L nativeCut index)
    (t : Nat) (g : Guard) (live : lookup c.state t = some g) (exclusive : g.kind = .exclusive) :
    c.state.counter g.cell = -1 := by
  have pos := live_guard_count_positive c t g live
  rw [exclusive] at pos
  rcases c.valid.2.1 g.cell with ⟨_, _, balance, unique, _⟩
  rcases unique pos with ⟨he, hs, hx⟩
  omega

theorem actual_guard_drop (trust : S2TrustedSdkBorrow L)
    (c : BorrowCut E original L nativeCut index) (t : Nat) (g : Guard)
    (live : lookup c.state t = some g) :
    Matches L (nativeCut E index) (.drop t) (release c.state g, .unit) := by
  cases hk : g.kind with
  | shared =>
    exact trust.shared_drop _ _ t g c.related c.valid live hk
      (shared_drop_counter_positive c t g live hk)
  | exclusive =>
    exact trust.exclusive_drop _ _ t g c.related c.valid live hk
      (exclusive_drop_counter_negative_one c t g live hk)

#print axioms live_guard_count_positive
#print axioms shared_drop_counter_positive
#print axioms exclusive_drop_counter_negative_one
#print axioms actual_guard_drop
end AspisR1.S2D
