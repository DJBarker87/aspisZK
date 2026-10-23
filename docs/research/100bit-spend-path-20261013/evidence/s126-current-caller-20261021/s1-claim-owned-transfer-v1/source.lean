import S1ClaimOwnedNestedModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer
abbrev E := aspis_core.field.WideExact
abbrev Range := core.ops.range.Range Usize

theorem scalar_eq {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Array U8 928#usize) (point l : Usize) :
    verifier.owned_scalar ops sem.claims sem.extra sem.before_z1 y1 point l =
      ClaimScalar.read ops sem (Array.to_slice y1) point l := by
  have hz : 0#usize ≤ point := by scalar_tac
  simp only [verifier.owned_scalar, ClaimScalar.read, hz, if_true, lift]
  split <;> simp only [bind_tc_ok]
  · rfl
  · split <;> rfl

theorem sum_eq (k parts : Array E 7#usize) :
    verifier.owned_sum k parts=verifier.prepared_claim_sum k parts := by rfl

/-- The full semantic owner is framed on both Rust success and Rust error.
This is not an assertion of successful/total execution or native equivalence. -/
theorem owner_frame {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem returned : r1_semantic.Verified H) (y1 : Array U8 928#usize)
    (inactive kappa : E) (g : Array E 29#usize) (r : core.result.Result E verifier.Error)
    (h : verifier.prepared_claim_owned ops inst sem y1 inactive g kappa = .ok (r,returned)) :
    returned=sem ∧ verifier.owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g kappa=.ok r := by
  unfold verifier.prepared_claim_owned at h
  cases hc : verifier.owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g kappa with
  | fail e => simp only [hc,bind_tc_fail] at h;cases h
  | div => simp only [hc,bind_tc_div] at h;cases h
  | ok value =>
    simp only [hc,bind_tc_ok] at h
    cases h
    exact ⟨rfl,rfl⟩

#print axioms scalar_eq
#print axioms sum_eq
#print axioms owner_frame
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
