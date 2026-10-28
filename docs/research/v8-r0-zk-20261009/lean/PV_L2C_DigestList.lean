import PV_L2C_DigestRange
set_option autoImplicit false
namespace PV_L2C_DigestList
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
abbrev Bytes := Array U8 32#usize
abbrev Digest := Array U32 8#usize
abbrev Error := atomic_statement.AtomicStatementError

/-- Ordered field-decode reference cut: first error is retained, and every
successful field is returned at its original position. -/
def run : List Bytes → Result (core.result.Result (List Digest) Error)
  | [] => ok (.Ok [])
  | b::bs => do
    let d ← atomic_statement.decode_digest_canonical b
    match d with
    | .Err e => ok (.Err e)
    | .Ok d =>
      let rest ← run bs
      match rest with
      | .Err e => ok (.Err e)
      | .Ok ds => ok (.Ok (d::ds))

theorem success (bytes : List Bytes) (ds : List Digest)
    (h : run bytes = ok (.Ok ds)) :
    ds.length = bytes.length ∧ ∀ d ∈ ds, ∀ x ∈ d.val, x.val < 2147483647 := by
  induction bytes generalizing ds with
  | nil => cases h; exact ⟨rfl,by simp⟩
  | cons b bs ih =>
    rw [run] at h
    pv_peel h with first hf
    cases first with
    | Err e => cases h
    | Ok d =>
      pv_peel h with rest hr
      cases rest with
      | Err e => cases h
      | Ok tail =>
        cases h
        obtain ⟨hlen,hcan⟩ := ih tail hr
        refine ⟨by simpa using hlen,?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with he | ht
        · subst v; exact PV_L2C_DigestRange.digest_success b d hf
        · exact hcan v ht
#print axioms success

theorem field (bytes : List Bytes) (ds : List Digest) (h : run bytes = ok (.Ok ds))
    (j : Nat) (hj : j < bytes.length) :
    ∃ d, ds[j]? = some d ∧ ∀ x ∈ d.val, x.val < 2147483647 := by
  obtain ⟨hl,hc⟩ := success bytes ds h
  have inside : j < ds.length := by omega
  exact ⟨ds[j],List.getElem?_eq_getElem inside,hc _ (List.getElem_mem inside)⟩
#print axioms field
end PV_L2C_DigestList
