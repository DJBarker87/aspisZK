import S1ClaimOwnedNestedModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer
abbrev E := aspis_core.field.WideExact
abbrev Range := core.ops.range.Range Usize

theorem scalar_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (point l : Usize) :
    verifier.owned_scalar ops sem.claims sem.extra sem.before_z1 y1 point l =
      ClaimScalar.read ops sem (Array.to_slice y1) point l := by
  have hz : 0#usize ≤ point := by scalar_tac
  simp only [verifier.owned_scalar, ClaimScalar.read, hz, if_true, lift]
  split <;> simp only [bind_tc_ok]
  · rfl

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

def finishPending {D : Type} (ops : ClaimDotOps D)
    (r : D × Option (core.result.Result E verifier.Error)) :
    Result (core.result.Result E verifier.Error) := do
  match r.2 with
  | none => let value ← ops.finishDot r.1; ok (.Ok value)
  | some result => ok result

def ownedStep {D H : Type} {N : Usize} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (point : Usize) (s : Range × D) :=
  verifier.owned_claim_loops_loop0_loop0.body ops sem.claims sem.extra sem.before_z1 y1 g point s.1 s.2

def ownedActive {D H : Type} {N : Usize} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (iter1 : Range) (point l : Usize) (dot : D) :
    Result (ControlFlow (Range × D) (D × Option (core.result.Result E verifier.Error))) := do
  let scalar ← ClaimScalar.read ops sem (Array.to_slice y1) point l
  let coeff ← Array.index_usize g l
  let (r,next) ← ops.pushDot dot coeff scalar
  let b ← ownedIsErr r
  if b then ok (.done (next,some (.Err verifier.Error.Parse))) else ok (.cont (iter1,next))

theorem owned_step_some {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (point l : Usize) (iter iter1 : Range) (dot : D)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some l,iter1)) :
    ownedStep ops sem y1 g point (iter,dot) = ownedActive ops sem y1 g iter1 point l dot := by
  unfold ownedStep verifier.owned_claim_loops_loop0_loop0.body
  rw [hn]
  simp only [bind_tc_ok,scalar_eq,verifier.owned_push,ownedActive,bind_assoc_eq]
  rfl

#print axioms scalar_eq
#print axioms sum_eq
#print axioms owner_frame
#print axioms owned_step_some
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
