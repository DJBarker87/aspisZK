import MultiproofConeCountPhysicalLevels

set_option autoImplicit false
namespace AspisR1.NBI_CountScan
attribute [local instance] Classical.propDecidable

/-- Native inner while: test one current cell before advancing it. -/
def scan (key : Nat → Nat) (parent n : Nat) : Nat → Nat → Nat
  | 0,j => j
  | fuel+1,j => if j < n ∧ key j / 2 = parent
      then scan key parent n fuel (j+1) else j

/-- Each one-step gate composes on the same key prestate. No final cursor
or assumed while-loop equation is used. -/
theorem scan_boundary (key : Nat → Nat) (parent n fuel j stop : Nat)
    (bounds : j ≤ stop ∧ stop ≤ n) (enough : stop-j ≤ fuel)
    (inside : ∀ k, j ≤ k → k < stop → key k / 2 = parent)
    (outside : stop = n ∨ key stop / 2 ≠ parent) :
    scan key parent n fuel j = stop := by
  induction fuel generalizing j with
  | zero =>
    have same : j = stop := by omega
    simp only [scan,same]
  | succ fuel ih =>
    by_cases active : j < stop
    · rw [scan,if_pos ⟨by omega,inside j (by omega) active⟩]
      exact ih (j+1) ⟨by omega,bounds.2⟩ (by omega)
        (fun k hk hs => inside k (by omega) hs)
    · have same : j = stop := by omega
      subst j
      rw [scan,if_neg (by rcases outside with h|h <;> simp_all)]

/-- Strict order proves the K006 group-width precondition (one or two),
including its exact stopping test. It is not an extra caller restriction. -/
theorem binary_group (key : Nat → Nat) (n i : Nat) (active : i < n)
    (ordered : ∀ a b, i ≤ a → a < b → b < n → key a < key b) :
    let stop := if i+1 < n ∧ key (i+1)/2 = key i/2 then i+2 else i+1
    i < stop ∧ stop ≤ n ∧ stop-i ≤ 2 ∧
    (∀ k, i ≤ k → k < stop → key k/2 = key i/2) ∧
    (stop = n ∨ key stop/2 ≠ key i/2) := by
  dsimp
  by_cases pair : i+1 < n ∧ key (i+1)/2 = key i/2
  · rw [if_pos pair]
    have adjacent := ordered i (i+1) (by omega) (by omega) pair.1
    refine ⟨by omega,by omega,by omega,?_,?_⟩
    · intro k lo hi
      have cases : k = i ∨ k = i+1 := by omega
      rcases cases with rfl|rfl
      · rfl
      · exact pair.2
    · by_cases last : i+2 = n
      · exact Or.inl last
      · right
        have third := ordered (i+1) (i+2) (by omega) (by omega) (by omega)
        omega
  · rw [if_neg pair]
    refine ⟨by omega,by omega,by omega,?_,?_⟩
    · intro k lo hi
      have : k = i := by omega
      subst k
      rfl
    · by_cases last : i+1 = n
      · exact Or.inl last
      · exact Or.inr (by intro h; exact pair ⟨by omega,h⟩)

/-- The inner source scan's exact endpoint and one/two-cell width, on the
same arbitrary sorted unread array as the native iteration. -/
theorem scan_group (key : Nat → Nat) (n i : Nat) (active : i < n)
    (ordered : ∀ a b, i ≤ a → a < b → b < n → key a < key b) :
    let stop := if i+1 < n ∧ key (i+1)/2 = key i/2 then i+2 else i+1
    scan key (key i/2) n (n-i) i = stop ∧ 1 ≤ stop-i ∧ stop-i ≤ 2 := by
  have domain := binary_group key n i active ordered
  dsimp at domain ⊢
  refine ⟨scan_boundary key (key i/2) n (n-i) i _ ⟨by omega,domain.2.1⟩
    (by omega) domain.2.2.2.1 domain.2.2.2.2,by omega,domain.2.2.1⟩

#print axioms scan_boundary
#print axioms binary_group
#print axioms scan_group
end AspisR1.NBI_CountScan
