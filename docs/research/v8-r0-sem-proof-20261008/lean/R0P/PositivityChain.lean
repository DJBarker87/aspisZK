import R0P.PositivityWired
import R0P.Copy

/-! Lead: positivity reduced to the copy registry.

`CopyLinkBalance` is the deterministic content of the LogUp argument: every
generated link's producer tuple equals its consumer tuple. The probabilistic
step (random λ, χ; `CHolds copyFamily` ⇒ balance except with small
probability) is the single remaining hypothesis and is not claimed here. -/
set_option autoImplicit false
namespace R0P
variable {K : Type} [Field K]

/-- Deterministic consequence of multiset balance over C:27–164. -/
def CopyLinkBalance (A : Trace K) : Prop :=
  ∀ link ∈ copyLinks, copyProducerTuple A link = copyConsumerTuple A link

theorem copy_balance_cell (A : Trace K) (link : CopyLink) (hmem : link ∈ copyLinks)
    (hb : CopyLinkBalance A) (t : K) (x y : K)
    (hp : copyProducerTuple A link = (t, fun i => if i = 0 then x else 0))
    (hc : copyConsumerTuple A link = (t, fun i => if i = 0 then y else 0)) : x = y := by
  have h := hb link hmem
  rw [hp, hc] at h
  have h0 := congrFun (congrArg Prod.snd h) 0
  simpa using h0

/-- The four copy equalities of `positivity_of_families` follow from balance. -/
theorem positivity_copy_cells (pub : Public K) (A : Trace K) (hb : CopyLinkBalance A) :
    A 10 1008 = A 0 1014 ∧ A 10 1010 = A 1 1014 ∧ A 10 1012 = A 1 1015 ∧
      A 2 1014 = A 0 1015 := by
  obtain ⟨hmem, hp0, hc0, hp1, hc1, hp2, hc2, hp3, hc3⟩ := copy_positivity_links pub A
  have m : ∀ link ∈ copyPositivityLinks, link ∈ copyLinks := fun l h => (hmem l h).1
  have l0 : copyPositivityLink0 ∈ copyPositivityLinks := by simp [copyPositivityLinks]
  have l1 : copyPositivityLink1 ∈ copyPositivityLinks := by simp [copyPositivityLinks]
  have l2 : copyPositivityLink2 ∈ copyPositivityLinks := by simp [copyPositivityLinks]
  have l3 : copyPositivityLink3 ∈ copyPositivityLinks := by simp [copyPositivityLinks]
  exact ⟨copy_balance_cell A _ (m _ l0) hb _ _ _ hp0 hc0,
    copy_balance_cell A _ (m _ l1) hb _ _ _ hp1 hc1,
    copy_balance_cell A _ (m _ l2) hb _ _ _ hp2 hc2,
    copy_balance_cell A _ (m _ l3) hb _ _ _ hp3 hc3⟩

/-- Integer positivity from the value and positive families plus copy balance. -/
theorem positivity_of_balance (P : Nat) [CharP K P] (hP : P = 2 ^ 31 - 1) (pub : Public K)
    (A : Trace K) (hv : Holds valueFamily pub A) (hpos : Holds positiveFamily pub A)
    (hb : CopyLinkBalance A) :
    ∃ v0 v1 v2 : Nat, v0 < 2 ^ 30 ∧ v1 < 2 ^ 30 ∧ v2 < 2 ^ 30 ∧ 1 ≤ v1 ∧ 1 ≤ v2 ∧
      v0 = v1 + v2 ∧ A 0 1014 = (v0 : K) ∧ A 1 1014 = (v1 : K) ∧ A 1 1015 = (v2 : K) := by
  obtain ⟨h0, h1, h2, h3⟩ := positivity_copy_cells pub A hb
  exact positivity_of_families P hP pub A hv hpos h0 h1 h2 h3

#print axioms copy_balance_cell
#print axioms positivity_copy_cells
#print axioms positivity_of_balance
end R0P
