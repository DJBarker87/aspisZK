import NGG_DecodeFinish

/-! Total exact-suffix theorem for the pinned, unedited Pool extraction.
The four bytes are parsed hints, not an authorization certificate. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGG_DecodePrefix
open NGG_SpineRef

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

/-- Symbolic strip followed by the full child Result; no admitted-account premise. -/
theorem cut {R : Type} (s : Slice U8) (decoded : core.result.Result R NGGSpineError)
    (count : Usize) (hlen : 4 ≤ s.val.length) :
    ∃ body : Slice U8, ∃ hints : Hints,
      NGG_SpineRef.decode_prefix s decoded count = ok (finish decoded count hints) ∧
      body.val = s.val.take (s.val.length-4) ∧
      s.val = body.val ++ [hints.current_page,hints.next_page,hints.vault_authority,hints.vault_token_account] := by
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
  let hints : Hints := ⟨v0,v1,v2,v3⟩
  refine ⟨body,hints,?_,?_,?_⟩
  · simp only [NGG_SpineRef.decode_prefix,lift,hsub,
      bind_tc_ok,NGG_SpineRef.core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,hsplit]
    change (do
      let x0 ← Slice.index_usize tail 0#usize
      let x1 ← Slice.index_usize tail 1#usize
      let x2 ← Slice.index_usize tail 2#usize
      let x3 ← Slice.index_usize tail 3#usize
      resume decoded count ⟨x0,x1,x2,x3⟩) = ok (finish decoded count hints)
    rw [h0]
    simp only [bind_tc_ok]
    rw [h1]
    simp only [bind_tc_ok]
    rw [h2]
    simp only [bind_tc_ok]
    rw [h3]
    simp only [bind_tc_ok]
    exact resume_eq decoded count hints
  · simpa only [hv'] using hbval
  · have hp := List.take_append_drop n.val s.val
    rw [← hbval, ← htval, ht] at hp
    simpa only [hints,hv0',hv1',hv2',hv3'] using hp.symm

#print axioms list_four
#print axioms cut
end NGG_DecodePrefix
