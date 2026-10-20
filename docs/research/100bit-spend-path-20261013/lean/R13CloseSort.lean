import R13CloseSortBody
import OccupancyRangeTraversal
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Sort
abbrev Keys := Array U64 16#usize
/-- Read set of the occupied key prefix, with repeated keys normalized. -/
def Prefix (a : Keys) (n : Nat) (x : U64) : Prop :=
  ∃ k, k < n ∧ a.val[k]! = x

def swapKeys (keys : Keys) (i j : Usize) : Result Keys := do
  let (s, back) ← lift (Array.to_slice_mut keys)
  let s1 ← core.slice.Slice.swap s i j
  ok (back s1)

theorem swap_prefix (keys out : Keys) (i j : Usize) (n : Nat)
    (hn : n ≤ 16) (hi : i.val < n) (hj : j.val < n)
    (h : swapKeys keys i j = ok out) :
    ∀ x, Prefix out n x ↔ Prefix keys n x := by
  have hlen : keys.val.length = 16 := keys.property
  obtain ⟨s', hs', hlen', hai, hbj, hframe⟩ := WP.spec_imp_exists
    (core.slice.Slice.swap_spec keys.to_slice i j (by simpa [Slice.length, hlen] using (show i.val < 16 by omega))
      (by simpa [Slice.length, hlen] using (show j.val < 16 by omega)))
  have he : keys.from_slice s' = out := by simpa [swapKeys, Array.to_slice_mut, lift, hs'] using h
  have hout : out.val = s'.val := by
    rw [← he]
    simp only [Array.from_slice]
    have hl : s'.val.length = (16#usize).val := by simpa [Slice.length] using hlen'
    simp only [hl, _root_.dite_true]
  have ha : out.val[i.val]! = keys.val[j.val]! := by simpa [hout, Array.to_slice] using hai
  have hb : out.val[j.val]! = keys.val[i.val]! := by simpa [hout, Array.to_slice] using hbj
  have hf : ∀ k, k ≠ i.val → k ≠ j.val → out.val[k]! = keys.val[k]! := by
    simpa [hout, Array.to_slice] using hframe
  intro x
  constructor
  · rintro ⟨k, hk, hx⟩
    by_cases hki : k = i.val
    · subst k; exact ⟨j.val, hj, ha.symm.trans hx⟩
    · by_cases hkj : k = j.val
      · subst k; exact ⟨i.val, hi, hb.symm.trans hx⟩
      · exact ⟨k, hk, (hf k hki hkj).symm.trans hx⟩
  · rintro ⟨k, hk, hx⟩
    by_cases hki : k = i.val
    · subst k; exact ⟨j.val, hj, hb.trans hx⟩
    · by_cases hkj : k = j.val
      · subst k; exact ⟨i.val, hi, ha.trans hx⟩
      · exact ⟨k, hk, (hf k hki hkj).trans hx⟩

/-- One actual insertion-sort step preserves the entire occupied key set. -/
theorem inner_body_prefix (keys : Keys) (j : Usize) (n : Nat)
    (hn : n ≤ 16) (hj : j.val < n) (r : ControlFlow (Keys × Usize) Keys)
    (h : verifier.candidate.sort_batch_keys_loop0_loop0.body keys j = ok r) :
    match r with
    | cont (out, j') => j'.val < n ∧ ∀ x, Prefix out n x ↔ Prefix keys n x
    | done out => ∀ x, Prefix out n x ↔ Prefix keys n x := by
  unfold verifier.candidate.sort_batch_keys_loop0_loop0.body at h
  split at h
  · obtain ⟨i, hi, h⟩ := bind_success h
    obtain ⟨left, hleft, h⟩ := bind_success h
    obtain ⟨right, hright, h⟩ := bind_success h
    have hsub := UScalar.sub_equiv j 1#usize
    rw [hi] at hsub
    have hi' : i.val < n := by
      have hpos : j.val > 0 := by assumption
      have h1 : (1#usize).val = 1 := rfl
      rw [h1] at hsub
      omega
    split at h
    · simp only [Array.to_slice_mut, lift, bind_tc_ok] at h
      obtain ⟨swapped, hswap, h⟩ := bind_success h
      have hout : swapKeys keys i j = ok (keys.from_slice swapped) := by
        simp [swapKeys, Array.to_slice_mut, lift, hswap]
      cases h
      exact ⟨hi', swap_prefix keys _ i j n hn hi' hj hout⟩
    · cases h; intro x; rfl
  · cases h; intro x; rfl

/-- Successful actual inner loops preserve key-prefix membership. -/
theorem inner_prefix (keys out : Keys) (j : Usize) (n : Nat)
    (hn : n ≤ 16) (hj : j.val < n)
    (h : verifier.candidate.sort_batch_keys_loop0_loop0 keys j = ok out) :
    ∀ x, Prefix out n x ↔ Prefix keys n x := by
  apply loop_invariant
    (fun s : Keys × Usize => verifier.candidate.sort_batch_keys_loop0_loop0.body s.1 s.2)
    (fun s => s.2.val < n ∧ ∀ x, Prefix s.1 n x ↔ Prefix keys n x)
    (fun out => ∀ x, Prefix out n x ↔ Prefix keys n x) ?_ ⟨hj, fun _ => Iff.rfl⟩ h
  rintro ⟨current, j'⟩ ⟨hj', hinv⟩ r hr
  have hs := inner_body_prefix current j' n hn hj' r hr
  cases r with
  | cont pair =>
    exact ⟨hs.1, fun x => (hs.2 x).trans (hinv x)⟩
  | done result => exact fun x => (hs x).trans (hinv x)

/-- The complete extracted insertion sort preserves exactly the key read
set of its n occupied slots. This does not yet prove ascending order. -/
theorem sort_prefix (keys out : Keys) (n : Usize) (hn : n.val ≤ 16)
    (h : verifier.candidate.sort_batch_keys keys n = ok out) :
    ∀ x, Prefix out n.val x ↔ Prefix keys n.val x := by
  unfold verifier.candidate.sort_batch_keys verifier.candidate.sort_batch_keys_loop0 at h
  apply loop_invariant
    (fun s : core.ops.range.Range Usize × Keys =>
      verifier.candidate.sort_batch_keys_loop0.body s.1 s.2)
    (fun s => s.1.end = n ∧ ∀ x, Prefix s.2 n.val x ↔ Prefix keys n.val x)
    (fun out => ∀ x, Prefix out n.val x ↔ Prefix keys n.val x) ?_ ⟨rfl, fun _ => Iff.rfl⟩ h
  rintro ⟨iter, current⟩ ⟨hend, hinv⟩ r hr
  change iter.end = n at hend
  unfold verifier.candidate.sort_batch_keys_loop0.body at hr
  by_cases hlt : iter.start.val < iter.end.val
  · obtain ⟨next, hnext, _, hnextend, _⟩ := AspisR1.OccupancyRangeTraversal.next_step iter hlt
    rw [hnext] at hr
    simp only [bind_tc_ok] at hr
    obtain ⟨sorted, hsorted, hr⟩ := bind_success hr
    have hs := inner_prefix current sorted iter.start n.val hn (by simpa [hend] using hlt) hsorted
    cases hr
    exact ⟨hnextend.trans hend, fun x => (hs x).trans (hinv x)⟩
  · rw [AspisR1.OccupancyRangeTraversal.next_done iter (by omega)] at hr
    simp only [bind_tc_ok] at hr
    cases hr
    exact hinv

#print axioms swap_prefix
#print axioms inner_body_prefix
#print axioms inner_prefix
#print axioms sort_prefix
end AspisR1Stage2.R13Close.Sort
