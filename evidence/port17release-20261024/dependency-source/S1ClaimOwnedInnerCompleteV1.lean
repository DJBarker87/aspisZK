import S1ClaimOwnedNestedLoopsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer
private theorem bind_ok_inv {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x)=.ok out) : ∃ x, m=.ok x ∧ k x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem owned_cont_next {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (point : Usize) (iter iter' : Range) (dot dot' : D)
    (h : ownedStep ops sem y1 g point (iter,dot)=.ok (.cont (iter',dot'))) :
    ∃ l, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some l,iter') := by
  rw [ownedStep_normal] at h
  obtain ⟨pair,hn,h⟩ := bind_ok_inv _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none => cases h
  | some l =>
    unfold ownedActive at h
    obtain ⟨scalar,_,h⟩ := bind_ok_inv _ _ _ h
    obtain ⟨coeff,_,h⟩ := bind_ok_inv _ _ _ h
    obtain ⟨pair,_,h⟩ := bind_ok_inv _ _ _ h
    rcases pair with ⟨r,dot1⟩
    cases r with
    | Err u => cases u;simp [ownedIsErr] at h
    | Ok u =>
      cases u
      change Result.ok (ControlFlow.cont (β := D × Option (core.result.Result E verifier.Error))
        (iter1,dot1)) = Result.ok (ControlFlow.cont (iter',dot')) at h
      have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      exact ⟨l,hn⟩

theorem owned_step_progress {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (point : Usize) (s next : Range × D)
    (hp : s.1.end.val=29 ∧ s.1.start.val≤29)
    (h : ownedStep ops sem y1 g point s=.ok (.cont next)) :
    (next.1.end.val=29 ∧ next.1.start.val≤29) ∧
      (30-next.1.start.val)+1=30-s.1.start.val := by
  rcases s with ⟨iter,dot⟩
  rcases next with ⟨iter',dot'⟩
  obtain ⟨l,hn⟩ := owned_cont_next ops sem y1 g point iter iter' dot dot' h
  obtain ⟨_,hactive,hstart,hend⟩ := ClaimTrace.next_some_step iter iter' l hn
  dsimp only at hp ⊢
  constructor
  · constructor
    · rw [hend];exact hp.1
    · omega
  · omega

theorem owned_loop_eq_bounded {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (point : Usize) (iter : Range) (dot : D)
    (hend : iter.end.val=29) (hstart : iter.start.val≤29) :
    verifier.owned_claim_loops_loop0_loop0 ops iter sem.claims sem.extra sem.before_z1 y1 g point dot =
      ClaimDotBoundedResult.bounded (ownedStep ops sem y1 g point) (30-iter.start.val) (iter,dot) := by
  apply ClaimDotBoundedResult.loop_eq_bounded (ownedStep ops sem y1 g point)
    (fun s => s.1.end.val=29 ∧ s.1.start.val≤29) (fun s => 30-s.1.start.val)
  · intro s hp;omega
  · exact owned_step_progress ops sem y1 g point
  · exact ⟨hend,hstart⟩
  · rfl

/-- Complete emitted nested-inner execution equals the retained source helper
loop after interpreting its pending Rust return. All child failures/divergence
are preserved; range control cannot exhaust its proven finite budget. -/
theorem complete_inner_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (point : Usize)
    (iter : Range) (dot : D) (hend : iter.end.val=29) (hstart : iter.start.val≤29) :
    (do let r ← verifier.owned_claim_loops_loop0_loop0 ops iter sem.claims sem.extra sem.before_z1 y1 g point dot
        finishPending ops r) =
      verifier.prepared_claim_dot_loop ops inst iter sem (Array.to_slice y1) g point dot := by
  rw [owned_loop_eq_bounded ops sem y1 g point iter dot hend hstart,
    ClaimDotBoundedResult.source_loop_eq_bounded ops inst iter sem (Array.to_slice y1) g point dot hend hstart]
  exact bounded_inner_eq ops inst sem y1 g point _ iter dot

#print axioms owned_cont_next
#print axioms owned_step_progress
#print axioms owned_loop_eq_bounded
#print axioms complete_inner_eq
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
