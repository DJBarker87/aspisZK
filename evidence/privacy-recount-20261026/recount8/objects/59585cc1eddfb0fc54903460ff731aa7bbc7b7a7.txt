import R0Z.HonestView
import R0P.CopyRegistry
import R0P.PositivityChain

/-! J0b, `helperSum` (LOG D40.4, D42.4): the literal LogUp helper sums to zero
over all 1024 rows for every trace satisfying `CopyLinkBalance`, at all λ, χ.

The argument is a re-indexing.  By `copy_producer_slots_nodup` and
`copy_consumer_slots_nodup` (CopyRegistry) each (row, slot) key carries at most
one producer and at most one consumer endpoint.  Hence the row-slot catalogue
`copyRowValues`/`copyRowWeights` at a key is either that single link's tuple
value and weight, or (0, 0); a (0, 0) slot contributes `(χ − 0)⁻¹ · 0 = 0`.
So `∑_r helper r = ∑_link (χ − p_link)⁻¹ w_link − ∑_link (χ − c_link)⁻¹ w_link`
(`sum_slots`), and `CopyLinkBalance` makes the two terms of every link equal:
a weight-zero link contributes zero on both sides, and an enabled link has
equal producer and consumer tuples, hence equal compressed values.

The zero-inverse (pole) convention is `helper`'s own: `Field.inv 0 = 0`; no
denominator is assumed nonzero, because the cancellation is termwise between
identical terms.  Nothing is assumed beyond `CopyLinkBalance pub t`. -/
set_option autoImplicit false
noncomputable section

namespace R0Z.HelperSum
open R0P R0Z.HonestView
attribute [local irreducible] copyLinks copyPatterns copyActiveRowMasks copyInactiveRows

variable {K : Type} [Field K]

/-! ### Re-indexing a slot catalogue with distinct keys -/

/-- The sum, over a list, of the entries keyed at (row r, slot s). -/
def slotSum {α : Type} (L : List α) (row : α → Fin 1024) (slot : α → Fin 2) (g : α → K)
    (r : Fin 1024) (s : Fin 2) : K :=
  (L.map (fun l => if row l = r ∧ slot l = s then g l else 0)).sum

theorem slotSum_nil {α : Type} (row : α → Fin 1024) (slot : α → Fin 2) (g : α → K)
    (r : Fin 1024) (s : Fin 2) : slotSum [] row slot g r s = 0 := rfl

theorem slotSum_cons {α : Type} (a : α) (L : List α) (row : α → Fin 1024) (slot : α → Fin 2)
    (g : α → K) (r : Fin 1024) (s : Fin 2) :
    slotSum (a :: L) row slot g r s =
      (if row a = r ∧ slot a = s then g a else 0) + slotSum L row slot g r s := by
  unfold slotSum
  rw [List.map_cons, List.sum_cons]

theorem slotSum_eq_zero {α : Type} (a : α) (L : List α) (row : α → Fin 1024)
    (slot : α → Fin 2) (g : α → K)
    (hn : (row a, slot a) ∉ L.map (fun l => (row l, slot l))) :
    slotSum L row slot g (row a) (slot a) = 0 := by
  unfold slotSum
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  have hne : ¬ (row l = row a ∧ slot l = slot a) := by
    rintro ⟨h1, h2⟩
    exact hn (List.mem_map.2 ⟨l, hl, Prod.ext h1 h2⟩)
  exact if_neg hne

theorem sum_single_slot {α : Type} (a : α) (row : α → Fin 1024) (slot : α → Fin 2) (c : K) :
    ∑ r : Fin 1024, ∑ s : Fin 2, (if row a = r ∧ slot a = s then c else 0) = c := by
  rw [Finset.sum_eq_single (row a), Finset.sum_eq_single (slot a)]
  · exact if_pos ⟨rfl, rfl⟩
  · intro s _ hs
    exact if_neg (fun h => hs h.2.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h
  · intro r _ hr
    exact Finset.sum_eq_zero (fun s _ => if_neg (fun h => hr h.1.symm))
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- With distinct (row, slot) keys, the row-slot sum of `(χ − value)⁻¹ · weight`
is the list sum of the same expression per entry.  Empty slots contribute
`(χ − 0)⁻¹ · 0 = 0`. -/
theorem sum_slots {α : Type} (L : List α) (row : α → Fin 1024) (slot : α → Fin 2)
    (v w : α → K) (chi : K) (hn : (L.map (fun l => (row l, slot l))).Nodup) :
    ∑ r : Fin 1024, ∑ s : Fin 2,
        (chi - slotSum L row slot v r s)⁻¹ * slotSum L row slot w r s =
      (L.map (fun l => (chi - v l)⁻¹ * w l)).sum := by
  induction L with
  | nil => simp only [slotSum_nil, mul_zero, Finset.sum_const_zero, List.map_nil, List.sum_nil]
  | cons a L ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    have key : ∀ (r : Fin 1024) (s : Fin 2),
        (chi - slotSum (a :: L) row slot v r s)⁻¹ * slotSum (a :: L) row slot w r s =
          (chi - slotSum L row slot v r s)⁻¹ * slotSum L row slot w r s +
            if row a = r ∧ slot a = s then (chi - v a)⁻¹ * w a else 0 := by
      intro r s
      rw [slotSum_cons, slotSum_cons]
      by_cases hc : row a = r ∧ slot a = s
      · obtain ⟨rfl, rfl⟩ := hc
        rw [slotSum_eq_zero a L row slot v hn.1, slotSum_eq_zero a L row slot w hn.1]
        simp only [and_self, ↓reduceIte, add_zero, sub_zero, mul_zero, zero_add]
      · simp only [if_neg hc, zero_add, add_zero]
    simp only [key, Finset.sum_add_distrib, ih hn.2, List.map_cons, List.sum_cons,
      sum_single_slot]
    exact add_comm _ _

/-! ### The literal helper -/

/-- `helper` in slot-catalogue form (definitional). -/
theorem helper_eq_slotSum (pub : Public K) (t : Trace K) (lam chi : K) (r : Fin 1024) :
    helper pub t lam chi r =
      (∑ s : Fin 2,
        (chi - slotSum copyLinks (fun l => l.producer.row) (fun l => l.producer.slot)
          (fun l => copyTupleValue lam (copyEndpointTuple t l.tag l.producer)) r s)⁻¹ *
        slotSum copyLinks (fun l => l.producer.row) (fun l => l.producer.slot)
          (fun l => copyLinkWeight l pub.nextPairIndex pub.variant) r s) -
      ∑ s : Fin 2,
        (chi - slotSum copyLinks (fun l => l.consumer.row) (fun l => l.consumer.slot)
          (fun l => copyTupleValue lam (copyEndpointTuple t l.tag l.consumer)) r s)⁻¹ *
        slotSum copyLinks (fun l => l.consumer.row) (fun l => l.consumer.slot)
          (fun l => copyLinkWeight l pub.nextPairIndex pub.variant) r s := rfl

/-- The row sum of the helper as a per-link difference (no balance used). -/
theorem sum_helper_eq_links (pub : Public K) (t : Trace K) (lam chi : K) :
    ∑ r, helper pub t lam chi r =
      (copyLinks.map (fun l =>
        (chi - copyTupleValue lam (copyEndpointTuple t l.tag l.producer))⁻¹ *
          copyLinkWeight l pub.nextPairIndex pub.variant)).sum -
      (copyLinks.map (fun l =>
        (chi - copyTupleValue lam (copyEndpointTuple t l.tag l.consumer))⁻¹ *
          copyLinkWeight l pub.nextPairIndex pub.variant)).sum := by
  simp only [helper_eq_slotSum, Finset.sum_sub_distrib]
  rw [sum_slots copyLinks (fun l => l.producer.row) (fun l => l.producer.slot)
      (fun l => copyTupleValue lam (copyEndpointTuple t l.tag l.producer))
      (fun l => copyLinkWeight l pub.nextPairIndex pub.variant) chi copy_producer_slots_nodup,
    sum_slots copyLinks (fun l => l.consumer.row) (fun l => l.consumer.slot)
      (fun l => copyTupleValue lam (copyEndpointTuple t l.tag l.consumer))
      (fun l => copyLinkWeight l pub.nextPairIndex pub.variant) chi copy_consumer_slots_nodup]

/-- J0b `helperSum`: for every trace with `CopyLinkBalance`, at all λ, χ. -/
theorem helperSum_of_balance (pub : Public K) (t : Trace K) (hb : CopyLinkBalance pub t)
    (lam chi : K) : ∑ r, helper pub t lam chi r = 0 := by
  rw [sum_helper_eq_links, sub_eq_zero]
  apply congrArg List.sum
  apply List.map_congr_left
  intro link hl
  by_cases hw : copyLinkWeight (K := K) link pub.nextPairIndex pub.variant = 0
  · simp only [hw, mul_zero]
  · have h := hb link hl hw
    change copyEndpointTuple t link.tag link.producer =
      copyEndpointTuple t link.tag link.consumer at h
    simp only [h]

#print axioms slotSum
#print axioms slotSum_nil
#print axioms slotSum_cons
#print axioms slotSum_eq_zero
#print axioms sum_single_slot
#print axioms sum_slots
#print axioms helper_eq_slotSum
#print axioms sum_helper_eq_links
#print axioms helperSum_of_balance
end R0Z.HelperSum
