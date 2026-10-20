import AspisR20Pool.Funs

/-! Total exact-suffix theorem for the pinned, unedited Pool extraction.
The four bytes are parsed hints, not an authorization certificate. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR20Pool.HintStrip
open pair_forest

private theorem list_four (xs : List U8) (h : xs.length = 4) :
    ∃ a b c d, xs = [a,b,c,d] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => simp at h
      | cons c xs =>
        cases xs with
        | nil => simp at h
        | cons d xs =>
          cases xs with
          | nil => exact ⟨a,b,c,d,rfl⟩
          | cons e xs => simp at h

/-- For every input of length at least four, execution succeeds, removes
exactly its final four bytes, and retains all four hints in their order. -/
theorem strip_total_exact (s : Slice U8) (hlen : 4 ≤ s.val.length) :
    ∃ body hints,
      split_pair_forest_terminal_bump_hints_v1 s = ok (.Ok (body,hints)) ∧
      body.val = s.val.take (s.val.length - 4) ∧
      s.val = body.val ++ [hints.current_page, hints.next_page,
        hints.vault_authority, hints.vault_token_account] := by
  obtain ⟨n, hn, hv⟩ := WP.spec_imp_exists
    (UScalar.sub_spec (x := Slice.len s) (y := 4#usize) (by simpa using hlen))
  have hv' : n.val = s.val.length - 4 := by simpa using hv.1
  have hsub : Usize.checked_sub (Slice.len s) 4#usize = some n := by
    simp only [Usize.checked_sub, core.num.checked_sub_UScalar, hn, Option.ofResult]
  obtain ⟨⟨body,tail⟩, hsplit, hb, htlen, hbval, htval⟩ := WP.spec_imp_exists
    (core.slice.Slice.split_at.spec s n (by change n.val ≤ s.val.length; omega))
  have htlen' : tail.val.length = 4 := by
    change tail.val.length = s.val.length - n.val at htlen
    omega
  obtain ⟨a,b,c,d,ht⟩ := list_four tail.val htlen'
  obtain ⟨v0,h0,hv0⟩ := WP.spec_imp_exists (Slice.index_usize_spec tail 0#usize (by simp [ht]))
  obtain ⟨v1,h1,hv1⟩ := WP.spec_imp_exists (Slice.index_usize_spec tail 1#usize (by simp [ht]))
  obtain ⟨v2,h2,hv2⟩ := WP.spec_imp_exists (Slice.index_usize_spec tail 2#usize (by simp [ht]))
  obtain ⟨v3,h3,hv3⟩ := WP.spec_imp_exists (Slice.index_usize_spec tail 3#usize (by simp [ht]))
  have hv0' : v0 = a := by simpa [ht] using hv0
  have hv1' : v1 = b := by simpa [ht] using hv1
  have hv2' : v2 = c := by simpa [ht] using hv2
  have hv3' : v3 = d := by simpa [ht] using hv3
  let hints : PoolV1PairForestTerminalBumpHintsV1 := ⟨v0,v1,v2,v3⟩
  refine ⟨body,hints,?_,?_,?_⟩
  · simp only [split_pair_forest_terminal_bump_hints_v1,
      POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES, lift, hsub,
      bind_tc_ok, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch, hsplit]
    simp only [h0,h1,h2,h3,bind_tc_ok]
    rfl
  · simpa only [hv'] using hbval
  · have hp := List.take_append_drop n.val s.val
    rw [← hbval, ← htval, ht] at hp
    simpa only [hints,hv0',hv1',hv2',hv3'] using hp.symm

#print axioms list_four
#print axioms strip_total_exact
end AspisR20Pool.HintStrip
