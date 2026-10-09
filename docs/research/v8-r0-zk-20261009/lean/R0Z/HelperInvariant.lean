import R0Z.MaskLayout
import R0Z.HonestView

/-! Eligible masks do not change any cell read by a Boolean-row copy
endpoint. The checks concern only literal endpoint descriptors and 16 small
pattern limbs, never a field, trace, encoder, or matrix. They are split into
bounded registry slices. The helper equality then follows symbolically. -/
set_option autoImplicit false
namespace R0Z.HelperInvariant
open R0P R0Z.MaskLayout R0Z.HonestView

local instance eligibleDec (c : Fin 29) (r : Fin 1024) : Decidable (eligible c r) := by
  unfold eligible forestPathUsed pairAuxUsed
  infer_instance

def Protected (ep : CopyEndpoint) : Prop :=
  ep.row ≠ 1023 ∧ ∀ i : Fin 16, (copyPatterns ep.pattern).kinds i = 1 →
    ¬ eligible (Fin.castLE (by omega) ((copyPatterns ep.pattern).columns i)) ep.row

local instance protectedDec (ep : CopyEndpoint) : Decidable (Protected ep) := by
  unfold Protected
  infer_instance

def checkLink (link : CopyLink) : Bool := decide (Protected link.producer ∧ Protected link.consumer)
def check (links : List CopyLink) : Bool := links.all checkLink

theorem check_spec (links : List CopyLink) (h : check links = true) :
    ∀ link ∈ links, Protected link.producer ∧ Protected link.consumer := by
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

theorem protected_registry (link : CopyLink) (hl : link ∈ copyLinks) :
    Protected link.producer ∧ Protected link.consumer := by
  apply check_spec copyLinks _ link hl
  rw [copyLinks, check_append, check_append, before_all, positive_all, after_all]
  rfl

noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows
variable {K : Type} [Field K] {F : Subfield K}

theorem protected_cell (t : Trace K) (e : EligibleNoise K F) (ep : CopyEndpoint)
    (hp : Protected ep) (i : Fin 16) (hi : (copyPatterns ep.pattern).kinds i = 1) :
    applyEligible t e (Fin.castLE (by omega) ((copyPatterns ep.pattern).columns i)) ep.row =
      t (Fin.castLE (by omega) ((copyPatterns ep.pattern).columns i)) ep.row := by
  simp only [applyEligible, Fin.val_castLE, if_pos ((copyPatterns ep.pattern).columns i).isLt,
    balance, if_neg hp.1, semanticNoise, dif_neg (hp.2 i hi), add_zero]

theorem protected_tuple (t : Trace K) (e : EligibleNoise K F) (tag : Nat)
    (ep : CopyEndpoint) (hp : Protected ep) :
    copyEndpointTuple (applyEligible t e) tag ep = copyEndpointTuple t tag ep := by
  refine Prod.ext rfl ?_
  funext i
  simp only [copyEndpointTuple, copyPatternTuple]
  by_cases hi : (copyPatterns ep.pattern).kinds i = 1
  · rw [if_pos hi, if_pos hi, protected_cell t e ep hp i hi]
  · rw [if_neg hi, if_neg hi]

theorem row_values_eligible (t : Trace K) (e : EligibleNoise K F) (lam : K)
    (r : Fin 1024) (endpoint : CopyLink → CopyEndpoint) (s : Fin 2)
    (hp : ∀ link ∈ copyLinks, Protected (endpoint link)) :
    copyRowValues (applyEligible t e) lam r endpoint s = copyRowValues t lam r endpoint s := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro link hl
  rw [protected_tuple t e link.tag (endpoint link) (hp link hl)]

theorem helper_eligible (pub : Public K) (t : Trace K) (e : EligibleNoise K F)
    (lam chi : K) (r : Fin 1024) :
    helper pub (applyEligible t e) lam chi r = helper pub t lam chi r := by
  have hp (s : Fin 2) := row_values_eligible t e lam r CopyLink.producer s
    (fun link hl => (protected_registry link hl).1)
  have hc (s : Fin 2) := row_values_eligible t e lam r CopyLink.consumer s
    (fun link hl => (protected_registry link hl).2)
  simp only [helper, copyRowsAt, hp, hc]

#print axioms protected_registry
#print axioms helper_eligible
end
end R0Z.HelperInvariant
