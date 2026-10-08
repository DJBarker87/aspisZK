import R0P.Copy

/-! G5 registry structure for the literal CopyLinks table C:27–164.
The three source blocks are kept visible throughout the tag proof; concrete
evaluation is limited to the three block records and their endpoint keys. -/
set_option autoImplicit false
namespace R0P

variable {K : Type} [Field K]

private theorem nodup_map_of_injOn {α β : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (f : α → β) (hn : xs.Nodup)
    (hinj : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have htail : xs.Nodup := (List.nodup_cons.mp hn).2
      have hnot : f a ∉ xs.map f := by
        intro hmem
        obtain ⟨b, hb, heq⟩ := List.mem_map.mp hmem
        have hab := hinj a (by simp) b (by simp [hb]) heq.symm
        exact (List.nodup_cons.mp hn).1 (hab ▸ hb)
      have hinjTail : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y := by
        intro x hx y hy heq
        exact hinj x (by simp [hx]) y (by simp [hy]) heq
      exact List.nodup_cons.mpr ⟨hnot, ih htail hinjTail⟩

private theorem length_filter_le_of_imp {α : Type} (xs : List α)
    (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    (xs.filter p).length ≤ (xs.filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hp : p x = true <;> by_cases hq : q x = true
      · simp [hp, hq, ih]
      · exact False.elim (by simpa [hq] using h x hp)
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte,
          List.length_cons] at *
        omega
      · simpa [hp, hq] using ih

private theorem length_filter_comp {α β : Type} [DecidableEq β]
    (xs : List α) (f : α → β) (q : β → Bool) :
    (xs.filter (fun x => q (f x))).length = ((xs.map f).filter q).length := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hq : q (f x) <;> simp [hq, ih]

private theorem key_row_filter_length_le_two {α : Type} [DecidableEq α]
    (xs : List (α × Fin 2)) (hn : xs.Nodup) (row : α) :
    (xs.filter (fun key => decide (key.1 = row))).length ≤ 2 := by
  classical
  let selected := xs.filter (fun key => decide (key.1 = row))
  have hs : selected.Nodup := hn.filter _
  have hinj : ∀ x ∈ selected, ∀ y ∈ selected, x.2 = y.2 → x = y := by
    intro x hx y hy hslot
    have hxrow := of_decide_eq_true (List.mem_filter.mp hx).2
    have hyrow := of_decide_eq_true (List.mem_filter.mp hy).2
    exact Prod.ext (hxrow.trans hyrow.symm) hslot
  have hslots : (selected.map Prod.snd).Nodup :=
    nodup_map_of_injOn selected Prod.snd hs hinj
  have hcard : (selected.map Prod.snd).length = (selected.map Prod.snd).toFinset.card := by
    symm
    exact List.toFinset_card_of_nodup hslots
  have hbound : (selected.map Prod.snd).toFinset.card ≤ 2 := by
    calc
      (selected.map Prod.snd).toFinset.card ≤ Finset.univ.card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = 2 := by rw [Finset.card_univ, Fintype.card_fin]
  simpa only [selected, List.length_map] using le_trans (le_of_eq hcard) hbound

private theorem list_all_eq_true_iff {α : Type} (xs : List α) (p : α → Bool) :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

private def list_disjoint_check {α : Type} [DecidableEq α] (xs ys : List α) : Bool :=
  xs.all (fun x => ys.all (fun y => decide (x ≠ y)))

private theorem list_disjoint_check_spec {α : Type} [DecidableEq α] (xs ys : List α)
    (h : list_disjoint_check xs ys = true) :
    ∀ x ∈ xs, ∀ y ∈ ys, x ≠ y := by
  intro x hx y hy hxy
  have hx' := (list_all_eq_true_iff xs _).mp h x hx
  have hy' := (list_all_eq_true_iff ys _).mp hx' y hy
  exact (of_decide_eq_true hy') hxy

def copyProducerRowSlots : List (Fin 1024 × Fin 2) :=
  copyLinks.map (fun link => (link.producer.row, link.producer.slot))

def copyConsumerRowSlots : List (Fin 1024 × Fin 2) :=
  copyLinks.map (fun link => (link.consumer.row, link.consumer.slot))

noncomputable def copyLinkEnabled (pub : Public K) (link : CopyLink) : Bool := by
  classical
  exact decide (copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)

noncomputable def copyProducerEnabledAtRow (pub : Public K) (b : Fin 1024)
    (link : CopyLink) : Bool := by
  classical
  exact decide (link.producer.row = b ∧
    copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)

noncomputable def copyConsumerEnabledAtRow (pub : Public K) (b : Fin 1024)
    (link : CopyLink) : Bool := by
  classical
  exact decide (link.consumer.row = b ∧
    copyLinkWeight (K := K) link pub.nextPairIndex pub.variant ≠ 0)

private theorem copyProducerRowSlots_before_nodup :
    (copyLinksBeforePositivity.map (fun link => (link.producer.row, link.producer.slot))).Nodup := by
  decide

private theorem copyProducerRowSlots_middle_nodup :
    (copyPositivityLinks.map (fun link => (link.producer.row, link.producer.slot))).Nodup := by
  decide

private theorem copyProducerRowSlots_after_nodup :
    (copyLinksAfterPositivity.map (fun link => (link.producer.row, link.producer.slot))).Nodup := by
  decide

private theorem copyProducerRowSlots_before_middle_disjoint :
    ∀ x ∈ copyLinksBeforePositivity.map (fun link => (link.producer.row, link.producer.slot)),
      ∀ y ∈ copyPositivityLinks.map (fun link => (link.producer.row, link.producer.slot)), x ≠ y := by
  exact list_disjoint_check_spec _ _ (by decide)

private theorem copyProducerRowSlots_before_after_disjoint :
    ∀ x ∈ copyLinksBeforePositivity.map (fun link => (link.producer.row, link.producer.slot)),
      ∀ y ∈ copyLinksAfterPositivity.map (fun link => (link.producer.row, link.producer.slot)), x ≠ y := by
  exact list_disjoint_check_spec _ _ (by decide)

private theorem copyProducerRowSlots_middle_after_disjoint :
    ∀ x ∈ copyPositivityLinks.map (fun link => (link.producer.row, link.producer.slot)),
      ∀ y ∈ copyLinksAfterPositivity.map (fun link => (link.producer.row, link.producer.slot)), x ≠ y := by
  exact list_disjoint_check_spec _ _ (by decide)

private theorem copyConsumerRowSlots_before_nodup :
    (copyLinksBeforePositivity.map (fun link => (link.consumer.row, link.consumer.slot))).Nodup := by
  decide

private theorem copyConsumerRowSlots_middle_nodup :
    (copyPositivityLinks.map (fun link => (link.consumer.row, link.consumer.slot))).Nodup := by
  decide

private theorem copyConsumerRowSlots_after_nodup :
    (copyLinksAfterPositivity.map (fun link => (link.consumer.row, link.consumer.slot))).Nodup := by
  decide

private theorem copyConsumerRowSlots_before_middle_disjoint :
    ∀ x ∈ copyLinksBeforePositivity.map (fun link => (link.consumer.row, link.consumer.slot)),
      ∀ y ∈ copyPositivityLinks.map (fun link => (link.consumer.row, link.consumer.slot)), x ≠ y := by
  exact list_disjoint_check_spec _ _ (by decide)

private theorem copyConsumerRowSlots_before_after_disjoint :
    ∀ x ∈ copyLinksBeforePositivity.map (fun link => (link.consumer.row, link.consumer.slot)),
      ∀ y ∈ copyLinksAfterPositivity.map (fun link => (link.consumer.row, link.consumer.slot)), x ≠ y := by
  exact list_disjoint_check_spec _ _ (by decide)

private theorem copyConsumerRowSlots_middle_after_disjoint :
    ∀ x ∈ copyPositivityLinks.map (fun link => (link.consumer.row, link.consumer.slot)),
      ∀ y ∈ copyLinksAfterPositivity.map (fun link => (link.consumer.row, link.consumer.slot)), x ≠ y := by
  exact list_disjoint_check_spec _ _ (by decide)

theorem copy_producer_slots_nodup :
    (copyLinks.map (fun link => (link.producer.row, link.producer.slot))).Nodup := by
  have hleft :
      (copyLinksBeforePositivity.map (fun link => (link.producer.row, link.producer.slot)) ++
        copyPositivityLinks.map (fun link => (link.producer.row, link.producer.slot))).Nodup :=
    List.nodup_append.mpr ⟨copyProducerRowSlots_before_nodup,
      copyProducerRowSlots_middle_nodup, copyProducerRowSlots_before_middle_disjoint⟩
  have hright := List.nodup_append.mpr ⟨hleft, copyProducerRowSlots_after_nodup, ?_⟩
  · simpa only [copyProducerRowSlots, copyLinks, List.map_append, List.append_assoc] using hright
  · intro key hkBefore other hkAfter heq
    rcases List.mem_append.mp hkBefore with hkBefore | hkMiddle
    · exact copyProducerRowSlots_before_after_disjoint key hkBefore other hkAfter heq
    · exact copyProducerRowSlots_middle_after_disjoint key hkMiddle other hkAfter heq

theorem copy_consumer_slots_nodup :
    (copyLinks.map (fun link => (link.consumer.row, link.consumer.slot))).Nodup := by
  have hleft :
      (copyLinksBeforePositivity.map (fun link => (link.consumer.row, link.consumer.slot)) ++
        copyPositivityLinks.map (fun link => (link.consumer.row, link.consumer.slot))).Nodup :=
    List.nodup_append.mpr ⟨copyConsumerRowSlots_before_nodup,
      copyConsumerRowSlots_middle_nodup, copyConsumerRowSlots_before_middle_disjoint⟩
  have hright := List.nodup_append.mpr ⟨hleft, copyConsumerRowSlots_after_nodup, ?_⟩
  · simpa only [copyConsumerRowSlots, copyLinks, List.map_append, List.append_assoc] using hright
  · intro key hkBefore other hkAfter heq
    rcases List.mem_append.mp hkBefore with hkBefore | hkMiddle
    · exact copyConsumerRowSlots_before_after_disjoint key hkBefore other hkAfter heq
    · exact copyConsumerRowSlots_middle_after_disjoint key hkMiddle other hkAfter heq

private theorem copy_tags_before :
    copyLinksBeforePositivity.map CopyLink.tag =
      (List.range 14).map (fun i => 1124073472 + i) := by
  decide

private theorem copy_tags_middle :
    copyPositivityLinks.map CopyLink.tag =
      (List.range 4).map (fun i => 1124073486 + i) := by
  decide

private theorem copy_tags_after :
    copyLinksAfterPositivity.map CopyLink.tag =
      (List.range 118).map (fun i => 1124073490 + i) := by
  decide

private theorem range_append_shift (start count : Nat) :
    List.range start ++ (List.range count).map (fun i => start + i) =
      List.range (start + count) := by
  induction count with
  | zero => simp
  | succ count ih =>
      have hstep :
          List.range start ++ (List.range count.succ).map (fun i => start + i) =
            (List.range start ++ (List.range count).map (fun i => start + i)) ++
              [start + count] := by
        rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
          ← List.append_assoc]
      calc
        List.range start ++ (List.range count.succ).map (fun i => start + i) =
            (List.range start ++ (List.range count).map (fun i => start + i)) ++
              [start + count] := hstep
        _ = List.range (start + count) ++ [start + count] := by rw [ih]
        _ = List.range (start + count.succ) := by
          rw [Nat.add_succ, List.range_succ]

private theorem range_map_base_add_shift (base start count : Nat) :
    (List.range start).map (fun i => base + i) ++
      (List.range count).map (fun i => base + (start + i)) =
        (List.range (start + count)).map (fun i => base + i) := by
  calc
    (List.range start).map (fun i => base + i) ++
    (List.range count).map (fun i => base + (start + i)) =
      (List.range start).map (fun i => base + i) ++
        ((List.range count).map (fun i => start + i)).map (fun i => base + i) := by
          congr 1
          rw [List.map_map]
          rfl
    _ = (List.range start ++ (List.range count).map (fun i => start + i)).map
        (fun i => base + i) := by rw [List.map_append]
    _ = (List.range (start + count)).map (fun i => base + i) := by
        rw [range_append_shift]

theorem copy_tags_indexed :
    copyLinks.map CopyLink.tag = (List.range 136).map (fun i => 1124073472 + i) := by
  rw [copyLinks, List.map_append, List.map_append, copy_tags_before, copy_tags_middle,
    copy_tags_after]
  have hmiddle :
      (List.range 4).map (fun i => 1124073486 + i) =
        (List.range 4).map (fun i => 1124073472 + (14 + i)) := by
    exact congrArg (fun f : Nat → Nat => (List.range 4).map f) (by
      funext i
      omega)
  have hafter :
      (List.range 118).map (fun i => 1124073490 + i) =
        (List.range 118).map (fun i => 1124073472 + (18 + i)) := by
    exact congrArg (fun f : Nat → Nat => (List.range 118).map f) (by
      funext i
      omega)
  have hfirst := range_map_base_add_shift 1124073472 14 4
  have hsecond := range_map_base_add_shift 1124073472 18 118
  have hfirst' :
      (List.range 14).map (fun i => 1124073472 + i) ++
        (List.range 4).map (fun i => 1124073472 + (14 + i)) =
          (List.range 18).map (fun i => 1124073472 + i) := by
    simpa using hfirst
  have hsecond' :
      (List.range 18).map (fun i => 1124073472 + i) ++
        (List.range 118).map (fun i => 1124073472 + (18 + i)) =
          (List.range 136).map (fun i => 1124073472 + i) := by
    simpa using hsecond
  rw [hmiddle, hafter]
  change
    (List.map (fun i => 1124073472 + i) (List.range 14) ++
      List.map (fun i => 1124073472 + (14 + i)) (List.range 4)) ++
      List.map (fun i => 1124073472 + (18 + i)) (List.range 118) =
      (List.range 136).map (fun i => 1124073472 + i)
  rw [hfirst', hsecond']

theorem copy_tags_nodup : (copyLinks.map CopyLink.tag).Nodup := by
  rw [copy_tags_indexed]
  apply nodup_map_of_injOn (List.range 136) (fun i => 1124073472 + i)
  · exact List.nodup_range
  · intro a ha b hb hab
    omega

theorem copy_enabled_endpoints_le (pub : Public K) :
  (copyLinks.filter (copyLinkEnabled pub)).length ≤ 136 := by
  classical
  have hbefore : copyLinksBeforePositivity.length = 14 := rfl
  have hmiddle : copyPositivityLinks.length = 4 := rfl
  have hafter : copyLinksAfterPositivity.length = 118 := rfl
  have hlinks : copyLinks.length = 136 := by
    change copyLinksBeforePositivity.length +
      (copyPositivityLinks.length + copyLinksAfterPositivity.length) = 136
    rw [← Nat.add_assoc]
    omega
  calc
    (copyLinks.filter (copyLinkEnabled pub)).length ≤
      copyLinks.length :=
        List.length_filter_le _ _
    _ = 136 := hlinks

theorem copy_active_row_producers_le (pub : Public K) (b : Fin 1024)
    (_hactive : CopyActiveRow b) :
    (copyLinks.filter (copyProducerEnabledAtRow pub b)).length ≤ 2 := by
  classical
  have hsub := length_filter_le_of_imp copyLinks
    (copyProducerEnabledAtRow pub b)
    (fun link => decide (link.producer.row = b)) (by
      intro link hp
      simp only [copyProducerEnabledAtRow, decide_eq_true_eq] at hp
      simpa only [decide_eq_true_eq] using hp.1)
  have hrow :
      (copyLinks.filter (fun link => decide (link.producer.row = b))).length =
        (copyProducerRowSlots.filter (fun key => decide (key.1 = b))).length := by
    exact length_filter_comp copyLinks (fun link => (link.producer.row, link.producer.slot))
      (fun key => decide (key.1 = b))
  calc
    (copyLinks.filter (copyProducerEnabledAtRow pub b)).length ≤
        (copyLinks.filter (fun link => decide (link.producer.row = b))).length := by
          exact hsub
    _ = (copyProducerRowSlots.filter (fun key => decide (key.1 = b))).length := hrow
    _ ≤ 2 := key_row_filter_length_le_two copyProducerRowSlots copy_producer_slots_nodup b

theorem copy_active_row_consumers_le (pub : Public K) (b : Fin 1024)
    (_hactive : CopyActiveRow b) :
    (copyLinks.filter (copyConsumerEnabledAtRow pub b)).length ≤ 2 := by
  classical
  have hsub := length_filter_le_of_imp copyLinks
    (copyConsumerEnabledAtRow pub b)
    (fun link => decide (link.consumer.row = b)) (by
      intro link hp
      simp only [copyConsumerEnabledAtRow, decide_eq_true_eq] at hp
      simpa only [decide_eq_true_eq] using hp.1)
  have hrow :
      (copyLinks.filter (fun link => decide (link.consumer.row = b))).length =
        (copyConsumerRowSlots.filter (fun key => decide (key.1 = b))).length := by
    exact length_filter_comp copyLinks (fun link => (link.consumer.row, link.consumer.slot))
      (fun key => decide (key.1 = b))
  calc
    (copyLinks.filter (copyConsumerEnabledAtRow pub b)).length ≤
        (copyLinks.filter (fun link => decide (link.consumer.row = b))).length := hsub
    _ = (copyConsumerRowSlots.filter (fun key => decide (key.1 = b))).length := hrow
    _ ≤ 2 := key_row_filter_length_le_two copyConsumerRowSlots copy_consumer_slots_nodup b

#print axioms nodup_map_of_injOn
#print axioms length_filter_le_of_imp
#print axioms length_filter_comp
#print axioms key_row_filter_length_le_two
#print axioms copyLinkEnabled
#print axioms copyProducerEnabledAtRow
#print axioms copyConsumerEnabledAtRow
#print axioms list_all_eq_true_iff
#print axioms list_disjoint_check
#print axioms list_disjoint_check_spec
#print axioms copyProducerRowSlots_before_nodup
#print axioms copyProducerRowSlots_middle_nodup
#print axioms copyProducerRowSlots_after_nodup
#print axioms copyProducerRowSlots_before_middle_disjoint
#print axioms copyProducerRowSlots_before_after_disjoint
#print axioms copyProducerRowSlots_middle_after_disjoint
#print axioms copyConsumerRowSlots_before_nodup
#print axioms copyConsumerRowSlots_middle_nodup
#print axioms copyConsumerRowSlots_after_nodup
#print axioms copyConsumerRowSlots_before_middle_disjoint
#print axioms copyConsumerRowSlots_before_after_disjoint
#print axioms copyConsumerRowSlots_middle_after_disjoint
#print axioms copy_producer_slots_nodup
#print axioms copy_consumer_slots_nodup
#print axioms copy_tags_before
#print axioms copy_tags_middle
#print axioms copy_tags_after
#print axioms range_append_shift
#print axioms range_map_base_add_shift
#print axioms copy_tags_indexed
#print axioms copy_tags_nodup
#print axioms copy_enabled_endpoints_le
#print axioms copy_active_row_producers_le
#print axioms copy_active_row_consumers_le

end R0P
