import PV_L2C_DigestRange
set_option autoImplicit false
namespace PV_L2C_OutputDecode
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder

structure Opening where
  owner : Array U8 32#usize
  salt : Array U8 32#usize
  value : U32

structure Output where
  owner : Array U32 8#usize
  salt : Array U32 8#usize
  value : U32

inductive Error where
  | noteOpening

/-- Owned reference to the wallet adapter's output_note cut. Both native
decoder calls and the first-error order are retained. -/
def run (n : Opening) : Result (core.result.Result Output Error) := do
  let owner ← atomic_statement.decode_digest_canonical n.owner
  match owner with
  | .Err _ => ok (.Err .noteOpening)
  | .Ok key =>
    let salt ← atomic_statement.decode_digest_canonical n.salt
    match salt with
    | .Err _ => ok (.Err .noteOpening)
    | .Ok s => ok (.Ok ⟨key,s,n.value⟩)

/-- The exact successful output, rather than an input normalization premise. -/
theorem success_iff (n : Opening) (out : Output) :
    run n = ok (.Ok out) ↔
      atomic_statement.decode_digest_canonical n.owner = ok (.Ok out.owner) ∧
      atomic_statement.decode_digest_canonical n.salt = ok (.Ok out.salt) ∧
      out.value = n.value := by
  constructor
  · intro h
    unfold run at h
    pv_peel h with owner howner
    cases owner with
    | Err e => cases h
    | Ok key =>
      pv_peel h with salt hsalt
      cases salt with
      | Err e => cases h
      | Ok s => cases h; exact ⟨howner,hsalt,rfl⟩
  · rintro ⟨ho,hs,hv⟩
    unfold run
    rw [ho]
    simp only [bind_tc_ok]
    rw [hs]
    simp only [bind_tc_ok]
    cases out
    cases hv
    rfl
#print axioms success_iff

theorem range (n : Opening) (out : Output) (h : run n = ok (.Ok out)) :
    (∀ x ∈ out.owner.val, x.val < 2147483647) ∧
    (∀ x ∈ out.salt.val, x.val < 2147483647) := by
  obtain ⟨ho,hs,_⟩ := (success_iff n out).mp h
  exact ⟨PV_L2C_DigestRange.digest_success n.owner out.owner ho,
    PV_L2C_DigestRange.digest_success n.salt out.salt hs⟩
#print axioms range

theorem no_raw_P (n : Opening) (out : Output) (h : run n = ok (.Ok out)) :
    2147483647#u32 ∉ out.owner.val ∧ 2147483647#u32 ∉ out.salt.val := by
  obtain ⟨ho,hs⟩ := range n out h
  constructor
  · intro hm
    exact Nat.lt_irrefl 2147483647 (ho _ hm)
  · intro hm
    exact Nat.lt_irrefl 2147483647 (hs _ hm)
#print axioms no_raw_P
end PV_L2C_OutputDecode
