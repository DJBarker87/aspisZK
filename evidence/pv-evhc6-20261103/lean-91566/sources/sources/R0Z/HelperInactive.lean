import R0Z.TerminalEligible

/-! J0b, `helperInactive` (LOG D40.4): every copy endpoint lies on a
copy-active row (registry fact, checked over bounded registry slices of the
literal endpoint descriptors and the 64-entry active-row mask table, as
`HelperInvariant.protected_registry`).  Hence the LogUp row values and weights
vanish on every inactive row, the literal helper is zero there, and
`∑_{r ∈ copyInactiveRows} helper pub t λ χ r = 0` for EVERY trace and all λ, χ.
This discharges the `helperInactive` field of `HonestBuilderSound`. -/
set_option autoImplicit false
namespace R0Z.HelperInactive
open R0P R0Z.MaskLayout R0Z.HonestView

def ActiveEnds (link : CopyLink) : Prop :=
  CopyActiveRow link.producer.row ∧ CopyActiveRow link.consumer.row

local instance activeDec (link : CopyLink) : Decidable (ActiveEnds link) := by
  unfold ActiveEnds
  infer_instance

def checkLink (link : CopyLink) : Bool := decide (ActiveEnds link)
def check (links : List CopyLink) : Bool := links.all checkLink

theorem check_spec (links : List CopyLink) (h : check links = true) :
    ∀ link ∈ links, ActiveEnds link := by
  simpa only [check, List.all_eq_true, checkLink, decide_eq_true_eq] using h

theorem check_append (xs ys : List CopyLink) : check (xs ++ ys) = (check xs && check ys) := by
  exact List.all_append

theorem check_take_drop (xs : List CopyLink) (n : Nat) :
    check xs = (check (xs.take n) && check (xs.drop n)) := by
  rw [← check_append, List.take_append_drop]

private theorem before_0 : check ((copyLinksBeforePositivity.drop 0).take 4) = true := by
  decide

private theorem before_4 : check ((copyLinksBeforePositivity.drop 4).take 4) = true := by
  decide

private theorem before_8 : check ((copyLinksBeforePositivity.drop 8).take 4) = true := by
  decide

private theorem before_12 : check ((copyLinksBeforePositivity.drop 12).take 4) = true := by
  decide

private theorem positive_0 : check ((copyPositivityLinks.drop 0).take 4) = true := by
  decide

private theorem after_0 : check ((copyLinksAfterPositivity.drop 0).take 4) = true := by
  decide

private theorem after_4 : check ((copyLinksAfterPositivity.drop 4).take 4) = true := by
  decide

private theorem after_8 : check ((copyLinksAfterPositivity.drop 8).take 4) = true := by
  decide

private theorem after_12 : check ((copyLinksAfterPositivity.drop 12).take 4) = true := by
  decide

private theorem after_16 : check ((copyLinksAfterPositivity.drop 16).take 4) = true := by
  decide

private theorem after_20 : check ((copyLinksAfterPositivity.drop 20).take 4) = true := by
  decide

private theorem after_24 : check ((copyLinksAfterPositivity.drop 24).take 4) = true := by
  decide

private theorem after_28 : check ((copyLinksAfterPositivity.drop 28).take 4) = true := by
  decide

private theorem after_32 : check ((copyLinksAfterPositivity.drop 32).take 4) = true := by
  decide

private theorem after_36 : check ((copyLinksAfterPositivity.drop 36).take 4) = true := by
  decide

private theorem after_40 : check ((copyLinksAfterPositivity.drop 40).take 4) = true := by
  decide

private theorem after_44 : check ((copyLinksAfterPositivity.drop 44).take 4) = true := by
  decide

private theorem after_48 : check ((copyLinksAfterPositivity.drop 48).take 4) = true := by
  decide

private theorem after_52 : check ((copyLinksAfterPositivity.drop 52).take 4) = true := by
  decide

private theorem after_56 : check ((copyLinksAfterPositivity.drop 56).take 4) = true := by
  decide

private theorem after_60 : check ((copyLinksAfterPositivity.drop 60).take 4) = true := by
  decide

private theorem after_64 : check ((copyLinksAfterPositivity.drop 64).take 4) = true := by
  decide

private theorem after_68 : check ((copyLinksAfterPositivity.drop 68).take 4) = true := by
  decide

private theorem after_72 : check ((copyLinksAfterPositivity.drop 72).take 4) = true := by
  decide

private theorem after_76 : check ((copyLinksAfterPositivity.drop 76).take 4) = true := by
  decide

private theorem after_80 : check ((copyLinksAfterPositivity.drop 80).take 4) = true := by
  decide

private theorem after_84 : check ((copyLinksAfterPositivity.drop 84).take 4) = true := by
  decide

private theorem after_88 : check ((copyLinksAfterPositivity.drop 88).take 4) = true := by
  decide

private theorem after_92 : check ((copyLinksAfterPositivity.drop 92).take 4) = true := by
  decide

private theorem after_96 : check ((copyLinksAfterPositivity.drop 96).take 4) = true := by
  decide

private theorem after_100 : check ((copyLinksAfterPositivity.drop 100).take 4) = true := by
  decide

private theorem after_104 : check ((copyLinksAfterPositivity.drop 104).take 4) = true := by
  decide

private theorem after_108 : check ((copyLinksAfterPositivity.drop 108).take 4) = true := by
  decide

private theorem after_112 : check ((copyLinksAfterPositivity.drop 112).take 4) = true := by
  decide

private theorem after_116 : check ((copyLinksAfterPositivity.drop 116).take 4) = true := by
  decide

private theorem before_all : check copyLinksBeforePositivity = true := by
  have h12 : check (copyLinksBeforePositivity.drop 12) = true := before_12
  have h8 : check (copyLinksBeforePositivity.drop 8) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, before_8, h12, Bool.true_and]
  have h4 : check (copyLinksBeforePositivity.drop 4) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, before_4, h8, Bool.true_and]
  have h0 : check (copyLinksBeforePositivity.drop 0) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, before_0, h4, Bool.true_and]
  exact h0

private theorem positive_all : check copyPositivityLinks = true := by
  have h0 : check (copyPositivityLinks.drop 0) = true := positive_0
  exact h0

private theorem after_all : check copyLinksAfterPositivity = true := by
  have h116 : check (copyLinksAfterPositivity.drop 116) = true := after_116
  have h112 : check (copyLinksAfterPositivity.drop 112) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_112, h116, Bool.true_and]
  have h108 : check (copyLinksAfterPositivity.drop 108) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_108, h112, Bool.true_and]
  have h104 : check (copyLinksAfterPositivity.drop 104) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_104, h108, Bool.true_and]
  have h100 : check (copyLinksAfterPositivity.drop 100) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_100, h104, Bool.true_and]
  have h96 : check (copyLinksAfterPositivity.drop 96) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_96, h100, Bool.true_and]
  have h92 : check (copyLinksAfterPositivity.drop 92) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_92, h96, Bool.true_and]
  have h88 : check (copyLinksAfterPositivity.drop 88) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_88, h92, Bool.true_and]
  have h84 : check (copyLinksAfterPositivity.drop 84) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_84, h88, Bool.true_and]
  have h80 : check (copyLinksAfterPositivity.drop 80) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_80, h84, Bool.true_and]
  have h76 : check (copyLinksAfterPositivity.drop 76) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_76, h80, Bool.true_and]
  have h72 : check (copyLinksAfterPositivity.drop 72) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_72, h76, Bool.true_and]
  have h68 : check (copyLinksAfterPositivity.drop 68) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_68, h72, Bool.true_and]
  have h64 : check (copyLinksAfterPositivity.drop 64) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_64, h68, Bool.true_and]
  have h60 : check (copyLinksAfterPositivity.drop 60) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_60, h64, Bool.true_and]
  have h56 : check (copyLinksAfterPositivity.drop 56) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_56, h60, Bool.true_and]
  have h52 : check (copyLinksAfterPositivity.drop 52) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_52, h56, Bool.true_and]
  have h48 : check (copyLinksAfterPositivity.drop 48) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_48, h52, Bool.true_and]
  have h44 : check (copyLinksAfterPositivity.drop 44) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_44, h48, Bool.true_and]
  have h40 : check (copyLinksAfterPositivity.drop 40) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_40, h44, Bool.true_and]
  have h36 : check (copyLinksAfterPositivity.drop 36) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_36, h40, Bool.true_and]
  have h32 : check (copyLinksAfterPositivity.drop 32) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_32, h36, Bool.true_and]
  have h28 : check (copyLinksAfterPositivity.drop 28) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_28, h32, Bool.true_and]
  have h24 : check (copyLinksAfterPositivity.drop 24) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_24, h28, Bool.true_and]
  have h20 : check (copyLinksAfterPositivity.drop 20) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_20, h24, Bool.true_and]
  have h16 : check (copyLinksAfterPositivity.drop 16) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_16, h20, Bool.true_and]
  have h12 : check (copyLinksAfterPositivity.drop 12) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_12, h16, Bool.true_and]
  have h8 : check (copyLinksAfterPositivity.drop 8) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_8, h12, Bool.true_and]
  have h4 : check (copyLinksAfterPositivity.drop 4) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_4, h8, Bool.true_and]
  have h0 : check (copyLinksAfterPositivity.drop 0) = true := by
    rw [check_take_drop _ 4]
    simp only [List.drop_drop, Nat.reduceAdd, after_0, h4, Bool.true_and]
  exact h0

theorem active_registry (link : CopyLink) (hl : link ∈ copyLinks) : ActiveEnds link := by
  apply check_spec copyLinks _ link hl
  rw [copyLinks, check_append, check_append, before_all, positive_all, after_all]
  rfl

noncomputable section
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
variable {K : Type} [Field K]

theorem rowValues_inactive (t : Trace K) (lam : K) (r : Fin 1024) (hr : ¬ CopyActiveRow r)
    (endpoint : CopyLink → CopyEndpoint) (hend : ∀ link ∈ copyLinks, CopyActiveRow (endpoint link).row)
    (s : Fin 2) : copyRowValues t lam r endpoint s = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨link, hl, rfl⟩ := List.mem_map.1 hv
  have hne : ¬ ((endpoint link).row = r ∧ (endpoint link).slot = s) := by
    rintro ⟨he, _⟩
    exact hr (he ▸ hend link hl)
  exact if_neg hne

theorem rowWeights_inactive (pub : Public K) (r : Fin 1024) (hr : ¬ CopyActiveRow r)
    (endpoint : CopyLink → CopyEndpoint) (hend : ∀ link ∈ copyLinks, CopyActiveRow (endpoint link).row)
    (s : Fin 2) : copyRowWeights pub r endpoint s = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨link, hl, rfl⟩ := List.mem_map.1 hv
  have hne : ¬ ((endpoint link).row = r ∧ (endpoint link).slot = s) := by
    rintro ⟨he, _⟩
    exact hr (he ▸ hend link hl)
  exact if_neg hne

/-- The literal helper vanishes on every inactive row. -/
theorem helper_inactive_zero (pub : Public K) (t : Trace K) (lam chi : K) (r : Fin 1024)
    (hr : ¬ CopyActiveRow r) : helper pub t lam chi r = 0 := by
  have hpw (s : Fin 2) := rowWeights_inactive pub r hr CopyLink.producer
    (fun link hl => (active_registry link hl).1) s
  have hcw (s : Fin 2) := rowWeights_inactive pub r hr CopyLink.consumer
    (fun link hl => (active_registry link hl).2) s
  simp only [helper, copyRowsAt, hpw, hcw, mul_zero, Finset.sum_const_zero, sub_zero]

/-- `helperInactive` for every trace and all λ, χ. -/
theorem helperInactive (pub : Public K) (t : Trace K) (lam chi : K) :
    ∑ r ∈ copyInactiveRows, helper pub t lam chi r = 0 := by
  apply Finset.sum_eq_zero
  intro r hr
  exact helper_inactive_zero pub t lam chi r ((R0Z.TerminalEligible.mem_inactive r).1 hr)

#print axioms active_registry
#print axioms rowValues_inactive
#print axioms rowWeights_inactive
#print axioms helper_inactive_zero
#print axioms helperInactive
end
end R0Z.HelperInactive
