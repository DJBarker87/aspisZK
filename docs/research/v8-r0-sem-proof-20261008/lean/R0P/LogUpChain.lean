import R0P.LogUpAssembly
import Mathlib.Data.Nat.Bitwise

/-!
Deterministic LogUp chain for the fixed `LogUpL1`–`LogUpL5` statements.

The literal Copy equations and endpoint folds are those of `R0P.Copy`
(pinned pair_forest_copy_terminal.rs:424–449,943–970; logup.rs:228–252).
L1 excludes all endpoint poles, including disabled endpoints. L2 regroups
only enabled endpoints. L1–L3 work over every field; L4–L5 use the lead's
M31 characteristic premise to recover bounded natural counts and tags.

The endpoint-mask coverage proof checks the three existing registry blocks,
with the user's explicit authorization; no trace or row universe is reduced.
All remaining list and finite-sum arguments are symbolic. No probabilistic
claim or new residual definition is introduced here.
-/

set_option autoImplicit false

/-!
G12 endpoint-coverage proof by bounded checks over the three source-defined
registry blocks. The Boolean checks reduce `copyLinksBeforePositivity` (14
records), `copyPositivityLinks` (4 records), and six bounded slices partitioning
`copyLinksAfterPositivity` (118 records). Each endpoint's source row determines
its mask block and local row; evaluation reads the corresponding bit from
`copyActiveRowMasks`. This method checks only those registry records and their
endpoint mask bits. It does not enumerate `Fin 1024`, inspect a trace, or
normalize `Finset.univ`. The `List.all` soundness argument, take/drop partition,
and append-membership glue are generic and symbolic. The proof supplies no
premise to, and makes no change to, fixed L2.
-/


namespace R0P

/-- Per-link check that both source endpoint rows are selected by the active
row masks. -/
def copyLinkEndpointsActiveCheck (link : CopyLink) : Bool :=
  decide (CopyActiveRow link.producer.row) && decide (CopyActiveRow link.consumer.row)

#print axioms copyLinkEndpointsActiveCheck

/-- Generic Boolean `List.all` checker over an arbitrary link list. -/
def copyLinksEndpointsActiveCheck (links : List CopyLink) : Bool :=
  links.all copyLinkEndpointsActiveCheck

#print axioms copyLinksEndpointsActiveCheck

private theorem copyLinkEndpointsActiveCheck_spec (link : CopyLink)
    (h : copyLinkEndpointsActiveCheck link = true) :
    CopyActiveRow link.producer.row ∧ CopyActiveRow link.consumer.row := by
  simp only [copyLinkEndpointsActiveCheck, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h

#print axioms copyLinkEndpointsActiveCheck_spec

private theorem copyLinksEndpointsActiveCheck_spec (links : List CopyLink)
    (h : copyLinksEndpointsActiveCheck links = true) :
    ∀ link ∈ links,
      CopyActiveRow link.producer.row ∧ CopyActiveRow link.consumer.row := by
  induction links with
  | nil => simp [copyLinksEndpointsActiveCheck] at h ⊢
  | cons head tail ih =>
      simp only [copyLinksEndpointsActiveCheck, List.all_cons, Bool.and_eq_true] at h
      intro link hmem
      rcases List.mem_cons.mp hmem with heq | htail
      · subst link
        exact copyLinkEndpointsActiveCheck_spec head h.1
      · exact ih h.2 link htail

#print axioms copyLinksEndpointsActiveCheck_spec

private theorem copyLinksEndpointsActiveCheck_take_drop (links : List CopyLink)
    (n : Nat) :
    copyLinksEndpointsActiveCheck links =
      (copyLinksEndpointsActiveCheck (links.take n) &&
        copyLinksEndpointsActiveCheck (links.drop n)) := by
  unfold copyLinksEndpointsActiveCheck
  rw [← List.all_append, List.take_append_drop]

#print axioms copyLinksEndpointsActiveCheck_take_drop

/-- Endpoint-mask check for the first source block of fourteen links. -/
private theorem copyLinksBeforePositivity_endpoints_active_check :
    copyLinksEndpointsActiveCheck copyLinksBeforePositivity = true := by
  decide

#print axioms copyLinksBeforePositivity_endpoints_active_check

/-- Endpoint-mask check for the four-link positivity block. -/
private theorem copyPositivityLinks_endpoints_active_check :
    copyLinksEndpointsActiveCheck copyPositivityLinks = true := by
  decide

#print axioms copyPositivityLinks_endpoints_active_check

/-- First bounded slice of the final source block. -/
private theorem copyLinksAfterPositivity_chunk0_check :
    copyLinksEndpointsActiveCheck (copyLinksAfterPositivity.take 20) = true := by
  decide

#print axioms copyLinksAfterPositivity_chunk0_check

private theorem copyLinksAfterPositivity_chunk1_check :
    copyLinksEndpointsActiveCheck ((copyLinksAfterPositivity.drop 20).take 20) = true := by
  decide

#print axioms copyLinksAfterPositivity_chunk1_check

private theorem copyLinksAfterPositivity_chunk2_check :
    copyLinksEndpointsActiveCheck ((copyLinksAfterPositivity.drop 40).take 20) = true := by
  decide

#print axioms copyLinksAfterPositivity_chunk2_check

private theorem copyLinksAfterPositivity_chunk3_check :
    copyLinksEndpointsActiveCheck ((copyLinksAfterPositivity.drop 60).take 20) = true := by
  decide

#print axioms copyLinksAfterPositivity_chunk3_check

private theorem copyLinksAfterPositivity_chunk4_check :
    copyLinksEndpointsActiveCheck ((copyLinksAfterPositivity.drop 80).take 20) = true := by
  decide

#print axioms copyLinksAfterPositivity_chunk4_check

private theorem copyLinksAfterPositivity_chunk5_check :
    copyLinksEndpointsActiveCheck (copyLinksAfterPositivity.drop 100) = true := by
  decide

#print axioms copyLinksAfterPositivity_chunk5_check

/-- The six bounded endpoint checks cover the complete source block by
symbolic `take`/`drop` decomposition. -/
private theorem copyLinksAfterPositivity_endpoints_active_check :
    copyLinksEndpointsActiveCheck copyLinksAfterPositivity = true := by
  rw [copyLinksEndpointsActiveCheck_take_drop copyLinksAfterPositivity 20,
    copyLinksEndpointsActiveCheck_take_drop (copyLinksAfterPositivity.drop 20) 20]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [copyLinksEndpointsActiveCheck_take_drop (copyLinksAfterPositivity.drop 40) 20]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [copyLinksEndpointsActiveCheck_take_drop (copyLinksAfterPositivity.drop 60) 20]
  simp only [List.drop_drop, Nat.reduceAdd]
  rw [copyLinksEndpointsActiveCheck_take_drop (copyLinksAfterPositivity.drop 80) 20]
  simp only [List.drop_drop, Nat.reduceAdd]
  simp [copyLinksAfterPositivity_chunk0_check, copyLinksAfterPositivity_chunk1_check,
    copyLinksAfterPositivity_chunk2_check, copyLinksAfterPositivity_chunk3_check,
    copyLinksAfterPositivity_chunk4_check, copyLinksAfterPositivity_chunk5_check]

#print axioms copyLinksAfterPositivity_endpoints_active_check

/-- Every link in the source registry has both endpoint rows selected by the
active-row masks, from the three block checks and symbolic append structure.
This is a coverage fact only; it does not modify any LogUp theorem statement. -/
theorem copyLinks_endpoints_active (link : CopyLink) (hlink : link ∈ copyLinks) :
    CopyActiveRow link.producer.row ∧ CopyActiveRow link.consumer.row := by
  rw [copyLinks] at hlink
  rcases List.mem_append.mp hlink with hbeforeMiddle | hafter
  · rcases List.mem_append.mp hbeforeMiddle with hbefore | hmiddle
    · exact copyLinksEndpointsActiveCheck_spec copyLinksBeforePositivity
        copyLinksBeforePositivity_endpoints_active_check link hbefore
    · exact copyLinksEndpointsActiveCheck_spec copyPositivityLinks
        copyPositivityLinks_endpoints_active_check link hmiddle
  · exact copyLinksEndpointsActiveCheck_spec copyLinksAfterPositivity
      copyLinksAfterPositivity_endpoints_active_check link hafter

#print axioms copyLinks_endpoints_active

end R0P

namespace R0P
open Classical

variable {K : Type} [Field K]

private theorem nat_and_one_zero_or_one (n : Nat) : n &&& 1 = 0 ∨ n &&& 1 = 1 := by
  have h : n &&& 1 = (n.testBit 0).toNat := by simpa using Nat.and_two_pow n 0
  rw [h]
  cases n.testBit 0 <;> simp

private theorem copy_link_weight_zero_or_one (pub : Public K) (link : CopyLink) :
      copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 0 ∨
      copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 1 := by
  generalize hk : link.weightKind = w
  fin_cases w
  · simp [copyLinkWeight, hk]
  · by_cases h : pub.variant = .privateTransfer <;> simp [copyLinkWeight, hk, h]
  · by_cases h : pub.variant = .withdrawal <;> simp [copyLinkWeight, hk, h]
  · rcases nat_and_one_zero_or_one (pub.nextPairIndex >>> link.weightLevel) with hb | hb
    · simp [copyLinkWeight, hk, hb]
    · simp [copyLinkWeight, hk, hb]
  · rcases nat_and_one_zero_or_one (pub.nextPairIndex >>> link.weightLevel) with hb | hb
    · simp [copyLinkWeight, hk, hb]
    · simp [copyLinkWeight, hk, hb]

private theorem copy_link_weight_one_of_ne_zero (pub : Public K) (link : CopyLink)
    (h : copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) :
    copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 1 := by
  rcases copy_link_weight_zero_or_one pub link with hz | ho
  · exact False.elim (h hz)
  · exact ho

private theorem copy_row_cross_fraction (chi p0 p1 c0 c1 pw0 pw1 cw0 cw1 h1 : K)
    (hp0 : chi - p0 ≠ 0) (hp1 : chi - p1 ≠ 0)
    (hc0 : chi - c0 ≠ 0) (hc1 : chi - c1 ≠ 0)
    (heq : ((chi - p0) * (chi - p1)) *
        (h1 * ((chi - c0) * (chi - c1)) +
          (cw0 * (chi - c1) + cw1 * (chi - c0))) =
      ((chi - c0) * (chi - c1)) *
        (pw0 * (chi - p1) + pw1 * (chi - p0))) :
    h1 = pw0 / (chi - p0) + pw1 / (chi - p1) -
      (cw0 / (chi - c0) + cw1 / (chi - c1)) := by
  field_simp [hp0, hp1, hc0, hc1] at heq ⊢
  linear_combination heq

private theorem sum_map_if_eq_filter {α : Type} (xs : List α)
    (p : α → Prop) [DecidablePred p] (f : α → K) :
    (xs.map (fun x => if p x then f x else 0)).sum =
      ((xs.filter p).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hp : p x <;> simp [hp, ih]

private theorem length_filter_map {α β : Type} (xs : List α) (f : α → β)
    (p : β → Bool) :
    (xs.filter (fun x => p (f x))).length = ((xs.map f).filter p).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hp : p (f x) = true <;> simp [hp, ih]

private theorem filter_foldr_add_eq_sum_map_if {α : Type} (xs : List α)
    (p : α → Prop) [DecidablePred p] (f : α → K) :
    (xs.filter p).foldr (fun x acc => acc + f x) 0 =
      (xs.map (fun x => if p x then f x else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hp : p x <;> simp [hp, ih, add_comm]

private theorem list_sum_split_fin2 {α : Type} (xs : List α)
    (slot : α → Fin 2) (f : α → K) :
    (xs.map f).sum =
      ((xs.filter (fun x => slot x = 0)).map f).sum +
        ((xs.filter (fun x => slot x = 1)).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      generalize hs : slot x = s
      fin_cases s <;> simp [hs, ih] <;> ac_rfl

private theorem pair_filter_length_le_one (xs : List (Fin 1024 × Fin 2))
    (hn : xs.Nodup) (b : Fin 1024) (slot : Fin 2) :
    (xs.filter (fun key => decide (key.1 = b ∧ key.2 = slot))).length ≤ 1 := by
  classical
  have hfiltered : (xs.filter (fun key => decide (key.1 = b ∧ key.2 = slot))).Nodup :=
    hn.filter _
  have hmem0 : ∀ key ∈ xs.filter (fun key => decide (key.1 = b ∧ key.2 = slot)),
      key = (b, slot) := by
    intro key hk
    have hp := of_decide_eq_true (List.mem_filter.mp hk).2
    exact Prod.ext hp.1 hp.2
  generalize hys : xs.filter (fun key => decide (key.1 = b ∧ key.2 = slot)) = ys
      at hfiltered hmem0 ⊢
  have hlen : ys.length ≤ 1 := by
    cases ys with
    | nil => simp
    | cons x xs =>
        have hxeq := hmem0 x (by simp)
        cases xs with
        | nil => simp
        | cons y ys =>
            have hyeq := hmem0 y (by simp)
            have hnot := (List.nodup_cons.mp hfiltered).1
            have hxy : x = y := hxeq.trans hyeq.symm
            exact False.elim (hnot (by rw [hxy]; simp))
  exact hlen

private def copyProducerSlotLinks (b : Fin 1024) (slot : Fin 2) : List CopyLink :=
  copyLinks.filter (fun link => decide (link.producer.row = b ∧ link.producer.slot = slot))

private def copyConsumerSlotLinks (b : Fin 1024) (slot : Fin 2) : List CopyLink :=
  copyLinks.filter (fun link => decide (link.consumer.row = b ∧ link.consumer.slot = slot))

private theorem copy_producer_slot_links_length_le_one (b : Fin 1024) (slot : Fin 2) :
    (copyProducerSlotLinks b slot).length ≤ 1 := by
  have hlen := length_filter_map copyLinks
    (fun link => (link.producer.row, link.producer.slot))
    (fun key => decide (key.1 = b ∧ key.2 = slot))
  change (copyLinks.filter (fun link =>
    decide (link.producer.row = b ∧ link.producer.slot = slot))).length ≤ 1
  rw [hlen]
  exact pair_filter_length_le_one copyProducerRowSlots copy_producer_slots_nodup b slot

private theorem copy_consumer_slot_links_length_le_one (b : Fin 1024) (slot : Fin 2) :
    (copyConsumerSlotLinks b slot).length ≤ 1 := by
  have hlen := length_filter_map copyLinks
    (fun link => (link.consumer.row, link.consumer.slot))
    (fun key => decide (key.1 = b ∧ key.2 = slot))
  change (copyLinks.filter (fun link =>
    decide (link.consumer.row = b ∧ link.consumer.slot = slot))).length ≤ 1
  rw [hlen]
  exact pair_filter_length_le_one copyConsumerRowSlots copy_consumer_slots_nodup b slot

private theorem copy_row_values_eq_producer_slot_sum (A : Trace K) (lam : K)
    (b : Fin 1024) (slot : Fin 2) :
    copyRowValues A lam b CopyLink.producer slot =
      ((copyProducerSlotLinks b slot).map (fun link => prodVal A lam link)).sum := by
  classical
  unfold copyRowValues copyProducerSlotLinks prodVal copyProducerTuple
  simp only [sum_map_if_eq_filter]

private theorem copy_row_weights_eq_producer_slot_sum (pub : Public K)
    (b : Fin 1024) (slot : Fin 2) :
    copyRowWeights pub b CopyLink.producer slot =
      ((copyProducerSlotLinks b slot).map
        (fun link => copyLinkWeight (K := K) link pub.nextPairIndex pub.variant)).sum := by
  classical
  unfold copyRowWeights copyProducerSlotLinks
  simp only [sum_map_if_eq_filter]

private theorem copy_row_values_eq_consumer_slot_sum (A : Trace K) (lam : K)
    (b : Fin 1024) (slot : Fin 2) :
    copyRowValues A lam b CopyLink.consumer slot =
      ((copyConsumerSlotLinks b slot).map (fun link => consVal A lam link)).sum := by
  classical
  unfold copyRowValues copyConsumerSlotLinks consVal copyConsumerTuple
  simp only [sum_map_if_eq_filter]

private theorem copy_row_weights_eq_consumer_slot_sum (pub : Public K)
    (b : Fin 1024) (slot : Fin 2) :
    copyRowWeights pub b CopyLink.consumer slot =
      ((copyConsumerSlotLinks b slot).map
        (fun link => copyLinkWeight (K := K) link pub.nextPairIndex pub.variant)).sum := by
  classical
  unfold copyRowWeights copyConsumerSlotLinks
  simp only [sum_map_if_eq_filter]

private theorem copy_producer_row_value_denominator_ne (A : Trace K) (lam chi : K)
    (b : Fin 1024) (slot : Fin 2) (hchi : chi ≠ 0)
    (hpole : chi ∉ poleSet A lam) :
    chi - copyRowValues A lam b CopyLink.producer slot ≠ 0 := by
  rw [copy_row_values_eq_producer_slot_sum]
  have hlen := copy_producer_slot_links_length_le_one b slot
  cases hx : copyProducerSlotLinks b slot with
  | nil => simp [hchi]
  | cons link tail =>
      have htail : tail = [] := by
        have : (link :: tail).length ≤ 1 := by simpa [hx] using hlen
        cases tail with
        | nil => rfl
        | cons y ys => simp at this
      subst tail
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hmem : link ∈ copyProducerSlotLinks b slot := by rw [hx]; simp
      have hlink : link ∈ copyLinks :=
        (List.mem_filter.mp (show link ∈ copyLinks.filter
          (fun l => decide (l.producer.row = b ∧ l.producer.slot = slot)) from hmem)).1
      have hpv : prodVal A lam link ∈ poleSet A lam := by
        simp only [poleSet, List.mem_toFinset, List.mem_append, List.mem_map]
        exact Or.inl ⟨link, hlink, rfl⟩
      apply sub_ne_zero.mpr
      intro he
      have hpole' : chi ∈ poleSet A lam := by rw [he]; exact hpv
      exact hpole hpole'

private theorem copy_consumer_row_value_denominator_ne (A : Trace K) (lam chi : K)
    (b : Fin 1024) (slot : Fin 2) (hchi : chi ≠ 0)
    (hpole : chi ∉ poleSet A lam) :
    chi - copyRowValues A lam b CopyLink.consumer slot ≠ 0 := by
  rw [copy_row_values_eq_consumer_slot_sum]
  have hlen := copy_consumer_slot_links_length_le_one b slot
  cases hx : copyConsumerSlotLinks b slot with
  | nil => simp [hchi]
  | cons link tail =>
      have htail : tail = [] := by
        have : (link :: tail).length ≤ 1 := by simpa [hx] using hlen
        cases tail with
        | nil => rfl
        | cons y ys => simp at this
      subst tail
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hmem : link ∈ copyConsumerSlotLinks b slot := by rw [hx]; simp
      have hlink : link ∈ copyLinks :=
        (List.mem_filter.mp (show link ∈ copyLinks.filter
          (fun l => decide (l.consumer.row = b ∧ l.consumer.slot = slot)) from hmem)).1
      have hcv : consVal A lam link ∈ poleSet A lam := by
        simp only [poleSet, List.mem_toFinset, List.mem_append, List.mem_map]
        exact Or.inr ⟨link, hlink, rfl⟩
      apply sub_ne_zero.mpr
      intro he
      have hpole' : chi ∈ poleSet A lam := by rw [he]; exact hcv
      exact hpole hpole'

private theorem copy_producer_slot_fraction (pub : Public K) (A : Trace K)
    (lam chi : K) (b : Fin 1024) (slot : Fin 2) :
    (((copyProducerSlotLinks b slot).filter (fun link =>
      copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)).map
        (fun link => 1 / (chi - prodVal A lam link))).sum =
      copyRowWeights pub b CopyLink.producer slot /
        (chi - copyRowValues A lam b CopyLink.producer slot) := by
  rw [copy_row_values_eq_producer_slot_sum, copy_row_weights_eq_producer_slot_sum]
  have hlen := copy_producer_slot_links_length_le_one b slot
  cases hx : copyProducerSlotLinks b slot with
  | nil => simp
  | cons link tail =>
      have htail : tail = [] := by
        have : (link :: tail).length ≤ 1 := by simpa [hx] using hlen
        cases tail with
        | nil => rfl
        | cons y ys => simp at this
      subst tail
      have hw := copy_link_weight_zero_or_one pub link
      rcases hw with hw | hw
      · simp [hw]
      · simp [hw]

private theorem copy_consumer_slot_fraction (pub : Public K) (A : Trace K)
    (lam chi : K) (b : Fin 1024) (slot : Fin 2) :
    (((copyConsumerSlotLinks b slot).filter (fun link =>
      copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)).map
        (fun link => 1 / (chi - consVal A lam link))).sum =
      copyRowWeights pub b CopyLink.consumer slot /
        (chi - copyRowValues A lam b CopyLink.consumer slot) := by
  rw [copy_row_values_eq_consumer_slot_sum, copy_row_weights_eq_consumer_slot_sum]
  have hlen := copy_consumer_slot_links_length_le_one b slot
  cases hx : copyConsumerSlotLinks b slot with
  | nil => simp
  | cons link tail =>
      have htail : tail = [] := by
        have : (link :: tail).length ≤ 1 := by simpa [hx] using hlen
        cases tail with
        | nil => rfl
        | cons y ys => simp at this
      subst tail
      have hw := copy_link_weight_zero_or_one pub link
      rcases hw with hw | hw
      · simp [hw]
      · simp [hw]

private theorem copy_producer_row_fold_eq_slot_sums (pub : Public K) (A : Trace K)
    (lam chi : K) (b : Fin 1024) :
    ((enabledLinks pub).filter (fun link => link.producer.row = b)).foldr
        (fun link acc => acc + 1 / (chi - prodVal A lam link)) 0 =
      (((copyProducerSlotLinks b 0).filter (fun link =>
        copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)).map
          (fun link => 1 / (chi - prodVal A lam link))).sum +
      (((copyProducerSlotLinks b 1).filter (fun link =>
        copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)).map
          (fun link => 1 / (chi - prodVal A lam link))).sum := by
  rw [filter_foldr_add_eq_sum_map_if, sum_map_if_eq_filter]
  let xs := (enabledLinks pub).filter (fun link => link.producer.row = b)
  have hsplit := list_sum_split_fin2 xs (fun link => link.producer.slot)
    (fun link => 1 / (chi - prodVal A lam link))
  have hslot (slot : Fin 2) :
      (xs.filter (fun link => link.producer.slot = slot)) =
        (copyProducerSlotLinks b slot).filter (fun link =>
          copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) := by
    unfold xs enabledLinks copyProducerSlotLinks copyLinkEnabled
    simp only [List.filter_filter]
    congr 1
    funext link
    simp only [Bool.decide_and, Bool.and_assoc, Bool.and_comm]
  rw [hslot 0, hslot 1] at hsplit
  exact hsplit

private theorem copy_consumer_row_fold_eq_slot_sums (pub : Public K) (A : Trace K)
    (lam chi : K) (b : Fin 1024) :
    ((enabledLinks pub).filter (fun link => link.consumer.row = b)).foldr
        (fun link acc => acc + 1 / (chi - consVal A lam link)) 0 =
      (((copyConsumerSlotLinks b 0).filter (fun link =>
        copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)).map
          (fun link => 1 / (chi - consVal A lam link))).sum +
      (((copyConsumerSlotLinks b 1).filter (fun link =>
        copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)).map
          (fun link => 1 / (chi - consVal A lam link))).sum := by
  rw [filter_foldr_add_eq_sum_map_if, sum_map_if_eq_filter]
  let xs := (enabledLinks pub).filter (fun link => link.consumer.row = b)
  have hsplit := list_sum_split_fin2 xs (fun link => link.consumer.slot)
    (fun link => 1 / (chi - consVal A lam link))
  have hslot (slot : Fin 2) :
      (xs.filter (fun link => link.consumer.slot = slot)) =
        (copyConsumerSlotLinks b slot).filter (fun link =>
          copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0) := by
    unfold xs enabledLinks copyConsumerSlotLinks copyLinkEnabled
    simp only [List.filter_filter]
    congr 1
    funext link
    simp only [Bool.decide_and, Bool.and_assoc, Bool.and_comm]
  rw [hslot 0, hslot 1] at hsplit
  exact hsplit

/-- L1: every active row's compressed Copy equation is its enabled reciprocal
row sum whenever χ is nonzero and avoids all endpoint values. -/
theorem logupL1 (pub : Public K) (A : Trace K) (lam chi : K) :
    LogUpL1 pub A lam chi := by
  intro hchi hpole hh b hb
  have hrow := (copy_holds_iff pub lam chi A).mp hh b hb
  change ((chi - copyRowValues A lam b CopyLink.producer 0) *
      (chi - copyRowValues A lam b CopyLink.producer 1)) *
      (A 26 b * ((chi - copyRowValues A lam b CopyLink.consumer 0) *
        (chi - copyRowValues A lam b CopyLink.consumer 1)) +
        (copyRowWeights pub b CopyLink.consumer 0 *
          (chi - copyRowValues A lam b CopyLink.consumer 1) +
         copyRowWeights pub b CopyLink.consumer 1 *
          (chi - copyRowValues A lam b CopyLink.consumer 0))) =
    ((chi - copyRowValues A lam b CopyLink.consumer 0) *
      (chi - copyRowValues A lam b CopyLink.consumer 1)) *
      (copyRowWeights pub b CopyLink.producer 0 *
        (chi - copyRowValues A lam b CopyLink.producer 1) +
       copyRowWeights pub b CopyLink.producer 1 *
        (chi - copyRowValues A lam b CopyLink.producer 0)) at hrow
  have hp0 := copy_producer_row_value_denominator_ne A lam chi b 0 hchi hpole
  have hp1 := copy_producer_row_value_denominator_ne A lam chi b 1 hchi hpole
  have hc0 := copy_consumer_row_value_denominator_ne A lam chi b 0 hchi hpole
  have hc1 := copy_consumer_row_value_denominator_ne A lam chi b 1 hchi hpole
  have hf := copy_row_cross_fraction chi
    (copyRowValues A lam b CopyLink.producer 0)
    (copyRowValues A lam b CopyLink.producer 1)
    (copyRowValues A lam b CopyLink.consumer 0)
    (copyRowValues A lam b CopyLink.consumer 1)
    (copyRowWeights pub b CopyLink.producer 0)
    (copyRowWeights pub b CopyLink.producer 1)
    (copyRowWeights pub b CopyLink.consumer 0)
    (copyRowWeights pub b CopyLink.consumer 1) (A 26 b)
    hp0 hp1 hc0 hc1 hrow
  rw [copy_producer_row_fold_eq_slot_sums, copy_consumer_row_fold_eq_slot_sums]
  rw [copy_producer_slot_fraction pub A lam chi b 0,
    copy_producer_slot_fraction pub A lam chi b 1,
    copy_consumer_slot_fraction pub A lam chi b 0,
    copy_consumer_slot_fraction pub A lam chi b 1]
  exact hf

#print axioms nat_and_one_zero_or_one
#print axioms copy_link_weight_zero_or_one
#print axioms copy_link_weight_one_of_ne_zero
#print axioms copy_row_cross_fraction
#print axioms sum_map_if_eq_filter
#print axioms length_filter_map
#print axioms pair_filter_length_le_one
#print axioms copyProducerSlotLinks
#print axioms copyConsumerSlotLinks
#print axioms copy_producer_slot_links_length_le_one
#print axioms copy_consumer_slot_links_length_le_one
#print axioms copy_row_values_eq_producer_slot_sum
#print axioms copy_row_weights_eq_producer_slot_sum
#print axioms copy_row_values_eq_consumer_slot_sum
#print axioms copy_row_weights_eq_consumer_slot_sum
#print axioms copy_producer_row_value_denominator_ne
#print axioms copy_consumer_row_value_denominator_ne
#print axioms filter_foldr_add_eq_sum_map_if
#print axioms copy_producer_slot_fraction
#print axioms copy_consumer_slot_fraction
#print axioms list_sum_split_fin2
#print axioms copy_producer_row_fold_eq_slot_sums
#print axioms copy_consumer_row_fold_eq_slot_sums
#print axioms logupL1

end R0P

noncomputable section
open Classical

namespace R0P
variable {K : Type} [Field K]

private theorem logup2_foldr_sum {α : Type} (xs : List α) (f : α → K) :
    xs.foldr (fun a acc => acc + f a) 0 = (xs.map f).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons, ih]
      exact add_comm _ _

#print axioms logup2_foldr_sum

/-- Partition an arbitrary list sum by a finite set covering its keys. -/
private theorem logup2_sum_fibers {α β : Type} [DecidableEq β] (xs : List α)
    (key : α → β) (f : α → K) (s : Finset β)
    (hkey : ∀ a ∈ xs, key a ∈ s) :
    (∑ b ∈ s, ((xs.filter (fun a => key a = b)).map f).sum) = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha : key a ∈ s := hkey a List.mem_cons_self
      have hxs : ∀ x ∈ xs, key x ∈ s := fun x hx => hkey x (List.mem_cons_of_mem a hx)
      have hterm (b : β) :
          (((a :: xs).filter (fun x => key x = b)).map f).sum =
            (if key a = b then f a else 0) + ((xs.filter (fun x => key x = b)).map f).sum := by
        by_cases h : key a = b <;> simp [h]
      have hone : (∑ b ∈ s, if key a = b then f a else 0) = f a := by
        rw [Finset.sum_eq_single (key a)]
        · exact if_pos rfl
        · intro b hb hba
          exact if_neg (Ne.symm hba)
        · intro hnot
          exact False.elim (hnot ha)
      simp_rw [hterm]
      rw [Finset.sum_add_distrib, hone, ih hxs]
      rfl

#print axioms logup2_sum_fibers

private theorem logup2_list_sum_constant {α : Type} (xs : List α)
    (f : α → K) (c : K) (hf : ∀ a ∈ xs, f a = c) :
    (xs.map f).sum = (xs.length : K) * c := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := hf a List.mem_cons_self
      have hxs : ∀ x ∈ xs, f x = c := fun x hx => hf x (List.mem_cons_of_mem a hx)
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, ha, ih hxs]
      ring

#print axioms logup2_list_sum_constant

private theorem logup2_sum_fibers_count {α β : Type} [DecidableEq β] (xs : List α)
    (key : α → β) (f : β → K) (s : Finset β)
    (hkey : ∀ a ∈ xs, key a ∈ s) :
    (∑ b ∈ s, (((xs.filter (fun a => key a = b)).length : Nat) : K) * f b) =
      (xs.map (fun a => f (key a))).sum := by
  rw [← logup2_sum_fibers xs key (fun a => f (key a)) s hkey]
  apply Finset.sum_congr rfl
  intro b hb
  symm
  apply logup2_list_sum_constant
  intro a ha
  have he : key a = b := of_decide_eq_true (List.mem_filter.mp ha).2
  exact congrArg f he

#print axioms logup2_sum_fibers_count

private theorem logup2_signed_fractions (pub : Public K) (t : Trace K) (lam chi : K) :
    (∑ v ∈ valueSet pub t lam, signedCount pub t lam v / (chi - v)) =
      ((enabledLinks pub).map (fun l => 1 / (chi - prodVal t lam l))).sum -
        ((enabledLinks pub).map (fun l => 1 / (chi - consVal t lam l))).sum := by
  have hp : ∀ l ∈ enabledLinks pub, prodVal t lam l ∈ valueSet pub t lam := by
    intro l hl
    simp only [valueSet, List.mem_toFinset, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨l, hl, rfl⟩)
  have hc : ∀ l ∈ enabledLinks pub, consVal t lam l ∈ valueSet pub t lam := by
    intro l hl
    simp only [valueSet, List.mem_toFinset, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨l, hl, rfl⟩)
  simp only [signedCount, sub_div, Finset.sum_sub_distrib]
  have hprod := logup2_sum_fibers_count (enabledLinks pub) (prodVal t lam)
    (fun v => 1 / (chi - v)) (valueSet pub t lam) hp
  have hcons := logup2_sum_fibers_count (enabledLinks pub) (consVal t lam)
    (fun v => 1 / (chi - v)) (valueSet pub t lam) hc
  simp only [mul_one_div] at hprod hcons
  rw [hprod, hcons]

#print axioms logup2_signed_fractions

/-- Sum the active-row identities, then regroup enabled endpoints by value. -/
private theorem logup2_of_endpoint_active
    (hcoverage : ∀ l ∈ copyLinks,
      CopyActiveRow l.producer.row ∧ CopyActiveRow l.consumer.row)
    (pub : Public K) (t : Trace K) (lam chi : K) : LogUpL2 pub t lam chi := by
  intro _hpole hrows htotal hinactive
  let active : Finset (Fin 1024) := Finset.univ.filter CopyActiveRow
  have hsplit : (∑ b ∈ active, t 26 b) + (∑ b ∈ copyInactiveRows, t 26 b) =
      ∑ b : Fin 1024, t 26 b := by
    simp only [active, copyInactiveRows, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : CopyActiveRow b <;> simp [h]
  have hactive : (∑ b ∈ active, t 26 b) = 0 := by
    rw [htotal, hinactive, add_zero] at hsplit
    exact hsplit
  have hp : ∀ l ∈ enabledLinks pub, l.producer.row ∈ active := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcoverage l (List.mem_filter.mp hl).1).1⟩
  have hc : ∀ l ∈ enabledLinks pub, l.consumer.row ∈ active := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcoverage l (List.mem_filter.mp hl).1).2⟩
  have hsum : (∑ b ∈ active, t 26 b) =
      (∑ b ∈ active, (((enabledLinks pub).filter (fun l => l.producer.row = b)).map
        (fun l => 1 / (chi - prodVal t lam l))).sum) -
      (∑ b ∈ active, (((enabledLinks pub).filter (fun l => l.consumer.row = b)).map
        (fun l => 1 / (chi - consVal t lam l))).sum) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [hrows b (Finset.mem_filter.mp hb).2, logup2_foldr_sum, logup2_foldr_sum]
  rw [logup2_sum_fibers (enabledLinks pub) (fun l : CopyLink => l.producer.row)
      (fun l => 1 / (chi - prodVal t lam l)) active hp,
    logup2_sum_fibers (enabledLinks pub) (fun l : CopyLink => l.consumer.row)
      (fun l => 1 / (chi - consVal t lam l)) active hc] at hsum
  rw [logup2_signed_fractions, ← hsum]
  exact hactive

#print axioms logup2_of_endpoint_active

/-- L2: the total and inactive helper sums imply the grouped fraction identity. -/
theorem logupL2 (pub : Public K) (t : Trace K) (lam chi : K) :
    LogUpL2 pub t lam chi :=
  logup2_of_endpoint_active copyLinks_endpoints_active pub t lam chi

#print axioms logupL2

end R0P
end

noncomputable section
open Classical

namespace R0P
open Polynomial

variable {K : Type} [Field K]

theorem logupL3 (pub : Public K) (t : Trace K) (lam chi : K) :
    LogUpL3 pub t lam chi := by
  intro hpole hbad hsum
  have hden : (∏ v ∈ valueSet pub t lam, (chi - v)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact sub_ne_zero.mpr (fun he => hpole (he ▸ hv))
  have hfrac := numer_partial_fraction (valueSet pub t lam)
    (signedCount pub t lam) chi hpole
  have heval : (numer (valueSet pub t lam) (signedCount pub t lam)).eval chi = 0 := by
    have he := hfrac.symm.trans hsum
    exact (div_eq_zero_iff.mp he).resolve_right hden
  have hzero : numer (valueSet pub t lam) (signedCount pub t lam) = 0 := by
    by_contra hn
    exact hbad ⟨hn, heval⟩
  exact numer_eq_zero_imp _ _ hzero

#print axioms logupL3

private theorem logup_natCast_inj (P : Nat) [CharP K P] {a b : Nat}
    (ha : a < P) (hb : b < P) (h : (a : K) = (b : K)) : a = b :=
  ((CharP.natCast_eq_natCast K P).mp h).eq_of_lt_of_lt ha hb

#print axioms logup_natCast_inj

omit [Field K] in
private theorem logup_count_map {α : Type} (xs : List α) (f : α → K) (v : K) :
    (((xs.map f : List K) : Multiset K).count v) =
      (xs.filter (fun a => f a = v)).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [Multiset.coe_count] at ih
      by_cases h : f a = v
      · simp [h, ih]
      · simp [h, ih]

#print axioms logup_count_map

private theorem logup_value_multisets (P : Nat) [CharP K P]
    (hP : P = 2^31-1) (pub : Public K) (t : Trace K) (lam : K)
    (hbal : ∀ v ∈ valueSet pub t lam, signedCount pub t lam v = 0) :
    (((enabledLinks pub).map (prodVal t lam) : List K) : Multiset K) =
      (((enabledLinks pub).map (consVal t lam) : List K) : Multiset K) := by
  have hlen : (enabledLinks pub).length ≤ 136 := copy_enabled_endpoints_le pub
  have hsmall : 136 < P := by rw [hP]; norm_num
  apply Multiset.ext.mpr
  intro v
  by_cases hv : v ∈ valueSet pub t lam
  · rw [logup_count_map, logup_count_map]
    apply logup_natCast_inj (K := K) P
    · exact (List.length_filter_le _ _).trans_lt (hlen.trans_lt hsmall)
    · exact (List.length_filter_le _ _).trans_lt (hlen.trans_lt hsmall)
    · exact sub_eq_zero.mp (hbal v hv)
  · have hp : v ∉ (((enabledLinks pub).map (prodVal t lam) : List K) : Multiset K) := by
      intro hm
      apply hv
      simp only [valueSet, List.mem_toFinset, List.mem_append]
      exact Or.inl hm
    have hc : v ∉ (((enabledLinks pub).map (consVal t lam) : List K) : Multiset K) := by
      intro hm
      apply hv
      simp only [valueSet, List.mem_toFinset, List.mem_append]
      exact Or.inr hm
    rw [Multiset.count_eq_zero_of_notMem hp, Multiset.count_eq_zero_of_notMem hc]

#print axioms logup_value_multisets

private theorem logup_compress_degree (tuple : K × (Fin 16 → K)) :
    (compressPoly tuple).natDegree ≤ 16 := by
  have hz : compressPoly ((0 : K), fun _ : Fin 16 => 0) = 0 := by
    simp only [compressPoly, map_zero, zero_mul, Finset.sum_const_zero, add_zero]
  simpa only [hz, sub_zero] using
    compressPoly_sub_natDegree_le tuple ((0 : K), fun _ : Fin 16 => 0)

#print axioms logup_compress_degree

private theorem logup_prodPolys_eval (pub : Public K) (t : Trace K) (lam : K) :
    (prodPolys pub t).map (fun q => q.eval lam) =
      (((enabledLinks pub).map (prodVal t lam) : List K) : Multiset K) := by
  simp only [prodPolys, Multiset.map_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, prodVal, copyTupleValue, compressPoly_eval, copy_powers_eq]

#print axioms logup_prodPolys_eval

private theorem logup_consPolys_eval (pub : Public K) (t : Trace K) (lam : K) :
    (consPolys pub t).map (fun q => q.eval lam) =
      (((enabledLinks pub).map (consVal t lam) : List K) : Multiset K) := by
  simp only [consPolys, Multiset.map_coe, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l _
  simp only [Function.comp_apply, consVal, copyTupleValue, compressPoly_eval, copy_powers_eq]

#print axioms logup_consPolys_eval

private theorem logup_root_product_map (S : Multiset K[X]) (lam : K) :
    (((S.map (fun q => (X : (K[X])[X]) - C q)).prod).map (evalRingHom lam)) =
      ((S.map (fun q => q.eval lam)).map (fun v => (X : K[X]) - C v)).prod := by
  rw [Polynomial.map_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Polynomial.coe_evalRingHom]

#print axioms logup_root_product_map

theorem logupL4 (P : Nat) [CharP K P] (hP : P = 2^31-1)
    (pub : Public K) (t : Trace K) (lam : K) : LogUpL4 pub t lam := by
  intro hbal hbad
  by_contra hne
  have hprod : ∀ q ∈ prodPolys pub t, q.natDegree ≤ 16 := by
    intro q hq
    change q ∈ (enabledLinks pub).map (fun l => compressPoly (copyProducerTuple t l)) at hq
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
    exact logup_compress_degree _
  have hcons : ∀ q ∈ consPolys pub t, q.natDegree ≤ 16 := by
    intro q hq
    change q ∈ (enabledLinks pub).map (fun l => compressPoly (copyConsumerTuple t l)) at hq
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hq
    exact logup_compress_degree _
  obtain ⟨_, k, hk, _⟩ := SemBadSets.product_difference_coeff
    (prodPolys pub t) (consPolys pub t) hne hprod hcons
  have hvals : (prodPolys pub t).map (fun q => q.eval lam) =
      (consPolys pub t).map (fun q => q.eval lam) := by
    rw [logup_prodPolys_eval, logup_consPolys_eval]
    exact logup_value_multisets P hP pub t lam hbal
  have hmap : ((((prodPolys pub t).map (fun q => (X : (K[X])[X]) - C q)).prod -
      ((consPolys pub t).map (fun q => X - C q)).prod).map (evalRingHom lam)) = 0 := by
    rw [Polynomial.map_sub, logup_root_product_map, logup_root_product_map, hvals, sub_self]
  have hc := congrArg (fun q : K[X] => q.coeff k) hmap
  have heval : ((((prodPolys pub t).map (fun q => (X : (K[X])[X]) - C q)).prod -
      ((consPolys pub t).map (fun q => X - C q)).prod).coeff k).eval lam = 0 := by
    simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom, Polynomial.coeff_zero] using hc
  exact hbad ⟨hne, k, hk, heval⟩

#print axioms logupL4

private theorem logup_tag_lt (P : Nat) (hP : P = 2^31-1)
    (l : CopyLink) (hl : l ∈ copyLinks) : l.tag < P := by
  have ht : l.tag ∈ copyLinks.map CopyLink.tag := List.mem_map.mpr ⟨l, hl, rfl⟩
  rw [copy_tags_indexed] at ht
  obtain ⟨i, hi, he⟩ := List.mem_map.mp ht
  have hir : i < 136 := List.mem_range.mp hi
  have hp : 1124073608 < P := by rw [hP]; norm_num
  omega

#print axioms logup_tag_lt

theorem logupL5 (P : Nat) [CharP K P] (hP : P = 2^31-1)
    (pub : Public K) (t : Trace K) : LogUpL5 pub t := by
  intro hpolys l hl hw
  have henabled : l ∈ enabledLinks pub := by
    simp only [enabledLinks, List.mem_filter, copyLinkEnabled, decide_eq_true_eq]
    exact ⟨hl, hw⟩
  have hmem : compressPoly (copyProducerTuple t l) ∈ prodPolys pub t := by
    change compressPoly (copyProducerTuple t l) ∈
      (enabledLinks pub).map (fun j => compressPoly (copyProducerTuple t j))
    exact List.mem_map.mpr ⟨l, henabled, rfl⟩
  rw [hpolys] at hmem
  change compressPoly (copyProducerTuple t l) ∈
    (enabledLinks pub).map (fun j => compressPoly (copyConsumerTuple t j)) at hmem
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hmem
  have hjlinks : j ∈ copyLinks := (List.mem_filter.mp hj).1
  have htuple := (compressPoly_eq_iff _ _).mp he
  have hcast := congrArg Prod.fst htuple
  change (j.tag : K) = (l.tag : K) at hcast
  have htags : j.tag = l.tag := logup_natCast_inj P
    (logup_tag_lt P hP j hjlinks) (logup_tag_lt P hP l hl) hcast
  have hjl : j = l := List.inj_on_of_nodup_map copy_tags_nodup hjlinks hl htags
  subst j
  exact htuple.symm

#print axioms logupL5

end R0P
end
