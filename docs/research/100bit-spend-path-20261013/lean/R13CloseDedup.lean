import R13CloseDedupBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Dedup

def PairIn (idx : Idx) (val : Val) (d : Nat) (q : U32 × Leaf) : Prop :=
  ∃ k, k < d ∧ idx.val[k]? = some q.1 ∧ val.val[k]? = some q.2

theorem read_success {A : Type} {n : Usize} (a : Array A n) (i : Usize) (x : A)
    (h : Array.index_usize a i = ok x) : a.val[i.val]? = some x := by
  unfold Array.index_usize at h
  split at h
  · cases h
  · rename_i old he
    cases h
    exact he

private theorem u8_ne (x y : U8) :
    core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  change WP.spec (ok (decide (x ≠ y))) _
  simp only [WP.spec_ok, decide_eq_true_eq]

theorem same_leaf_success (val : Val) (i : Usize) (leaf : Leaf)
    (h : verifier.candidate.same_batch_leaf val i leaf = ok true) :
    val.val[i.val]? = some leaf := by
  unfold verifier.candidate.same_batch_leaf at h
  obtain ⟨a, ha, h⟩ := bind_success h
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8
    a.to_slice leaf.to_slice u8_ne
  change WP.spec (core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a leaf)
    (fun b => b ↔ a.to_slice = leaf.to_slice) at hs
  obtain ⟨b, hb, he⟩ := WP.spec_imp_exists hs
  rw [h] at hb
  cases hb
  have heq : a = leaf := Subtype.ext (congrArg (fun s : Slice U8 => s.val) (he.mp rfl))
  subst a
  exact read_success val i leaf ha

/-- Exact pair-set effect of append-at-d, independent of the unused suffix. -/
theorem append_pairs (idx idx' : Idx) (val val' : Val) (d : Usize)
    (index : U32) (leaf : Leaf)
    (hidx : Array.update idx d index = ok idx')
    (hval : Array.update val d leaf = ok val') :
    ∀ q, PairIn idx' val' (d.val + 1) q ↔
      PairIn idx val d.val q ∨ q = (index, leaf) := by
  obtain ⟨hbi, hidx⟩ := update_success idx idx' d index hidx
  obtain ⟨hbv, hval⟩ := update_success val val' d leaf hval
  intro q
  constructor
  · rintro ⟨k, hk, hi, hv⟩
    by_cases he : k = d.val
    · subst k
      rw [hidx, List.getElem?_set_self hbi] at hi
      rw [hval, List.getElem?_set_self hbv] at hv
      exact Or.inr (Prod.ext (Option.some.inj hi).symm (Option.some.inj hv).symm)
    · rw [hidx, List.getElem?_set_ne (Ne.symm he)] at hi
      rw [hval, List.getElem?_set_ne (Ne.symm he)] at hv
      exact Or.inl ⟨k, by omega, hi, hv⟩
  · intro h
    rcases h with ⟨k, hk, hi, hv⟩ | rfl
    · refine ⟨k, by omega, ?_, ?_⟩
      · rw [hidx, List.getElem?_set_ne (by omega : d.val ≠ k)]; exact hi
      · rw [hval, List.getElem?_set_ne (by omega : d.val ≠ k)]; exact hv
    · exact ⟨d.val, by omega, by rw [hidx, List.getElem?_set_self hbi],
        by rw [hval, List.getElem?_set_self hbv]⟩

/-- Every continuing source dedup step adds precisely its current pair to
support. Duplicate retention is justified by the actual byte comparison. -/
theorem dedup_step_pairs (idx idx' : Idx) (val val' : Val) (d d' pos pos' : Usize)
    (index : U32) (leaf : Leaf)
    (h : dedupStep idx val d pos index leaf = ok (cont (idx', val', d', pos'))) :
    pos' = pos ∧ ∀ q, PairIn idx' val' d'.val q ↔
      PairIn idx val d.val q ∨ q = (index, leaf) := by
  unfold dedupStep at h
  split at h
  · obtain ⟨last, hlast, h⟩ := bind_success h
    obtain ⟨same, hsame, h⟩ := bind_success h
    cases same with
    | true =>
      obtain ⟨equal, hequal, h⟩ := bind_success h
      cases equal with
      | false => cases h
      | true =>
        cases h
        obtain ⟨old, hold, hsame'⟩ := bind_success hsame
        have heq : old = index := by simpa using hsame'
        have hi : idx.val[last.val]? = some index := by
          subst old
          exact read_success idx last index hold
        have hv := same_leaf_success val last leaf hequal
        have hs := UScalar.sub_equiv d 1#usize
        rw [hlast] at hs
        have hlast' : last.val < d.val := by
          have h1 : (1#usize).val = 1 := rfl
          rw [h1] at hs
          omega
        have hmember : PairIn idx val d.val (index, leaf) := ⟨last.val, hlast', hi, hv⟩
        refine ⟨rfl, ?_⟩
        intro q
        constructor
        · exact Or.inl
        · intro hq; rcases hq with hq | rfl
          · exact hq
          · exact hmember
    | false =>
      obtain ⟨newIdx, hidx, h⟩ := bind_success h
      obtain ⟨newVal, hval, h⟩ := bind_success h
      obtain ⟨next, hnext, h⟩ := bind_success h
      have hs := UScalar.add_equiv d 1#usize
      rw [hnext] at hs
      cases h
      exact ⟨rfl, by simpa only [show (1#usize).val = 1 from rfl, hs.2.1] using
        (append_pairs idx _ val _ d index leaf hidx hval)⟩
  · obtain ⟨newIdx, hidx, h⟩ := bind_success h
    obtain ⟨newVal, hval, h⟩ := bind_success h
    obtain ⟨next, hnext, h⟩ := bind_success h
    have hs := UScalar.add_equiv d 1#usize
    rw [hnext] at hs
    cases h
    exact ⟨rfl, by simpa only [show (1#usize).val = 1 from rfl, hs.2.1] using
      (append_pairs idx _ val _ d index leaf hidx hval)⟩

#print axioms read_success
#print axioms u8_ne
#print axioms same_leaf_success
#print axioms append_pairs
#print axioms dedup_step_pairs
end AspisR1Stage2.R13Close.Dedup
