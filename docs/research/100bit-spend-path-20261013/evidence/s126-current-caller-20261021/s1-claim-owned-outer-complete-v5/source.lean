import S1ClaimOwnedOuterStepV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer

private theorem bind_ok_inv {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x)=.ok out) : ∃ x, m=.ok x ∧ k x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h
  | ok x => exact ⟨x,rfl,h⟩

theorem owned_outer_cont_next {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (iter iter' : Range) (parts parts' : Parts)
    (h : ownedOuterStep ops sem y1 g (iter,parts)=.ok (.cont (iter',parts'))) :
    ∃ point, core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=.ok (some point,iter') := by
  unfold ownedOuterStep verifier.owned_claim_loops_loop0.body at h
  obtain ⟨pair,hn,h⟩ := bind_ok_inv _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none => cases h
  | some point =>
    obtain ⟨dot,_,h⟩ := bind_ok_inv _ _ _ h
    obtain ⟨pair,_,h⟩ := bind_ok_inv _ _ _ h
    rcases pair with ⟨dot1,pending⟩
    cases pending with
    | some r => cases h
    | none =>
      obtain ⟨value,_,h⟩ := bind_ok_inv _ _ _ h
      obtain ⟨i,_,h⟩ := bind_ok_inv _ _ _ h
      obtain ⟨next,_,h⟩ := bind_ok_inv _ _ _ h
      have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      exact ⟨point,hn⟩

theorem owned_outer_progress {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (s next : OuterState) (hp : s.1.end.val=6 ∧ s.1.start.val≤6)
    (h : ownedOuterStep ops sem y1 g s=.ok (.cont next)) :
    (next.1.end.val=6 ∧ next.1.start.val≤6) ∧ (7-next.1.start.val)+1=7-s.1.start.val := by
  rcases s with ⟨iter,parts⟩
  rcases next with ⟨iter',parts'⟩
  obtain ⟨point,hn⟩ := owned_outer_cont_next ops sem y1 g iter iter' parts parts' h
  obtain ⟨_,hactive,hstart,hend⟩ := ClaimTrace.next_some_step iter iter' point hn
  dsimp only at hp ⊢
  constructor
  · constructor
    · rw [hend];exact hp.1
    · omega
  · omega

theorem owned_outer_loop_eq_bounded {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (iter : Range) (parts : Parts) (hend : iter.end.val=6) (hstart : iter.start.val≤6) :
    verifier.owned_claim_loops_loop0 ops iter sem.claims sem.extra sem.before_z1 y1 g parts =
      ClaimDotBoundedResult.bounded (ownedOuterStep ops sem y1 g) (7-iter.start.val) (iter,parts) := by
  apply ClaimDotBoundedResult.loop_eq_bounded (ownedOuterStep ops sem y1 g)
    (fun s => s.1.end.val=6 ∧ s.1.start.val≤6) (fun s => 7-s.1.start.val)
  · intro s hp;omega
  · exact owned_outer_progress ops sem y1 g
  · exact ⟨hend,hstart⟩
  · rfl

def refOuterStep {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (k : Parts) (s : OuterState) :=
  verifier.prepared_claim_loop.body ops inst sem (Array.to_slice y1) g k s.1 s.2

theorem bounded_outer_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (k : Parts) (n : Nat) (s : OuterState) :
    (do let out ← ClaimDotBoundedResult.bounded (ownedOuterStep ops sem y1 g) n s;finishOuter k out) =
      ClaimDotBoundedResult.bounded (refOuterStep ops inst sem y1 g k) n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rcases s with ⟨iter,parts⟩
    let kont : OuterState → Result RustClaim := fun next => do
      let out ← ClaimDotBoundedResult.bounded (ownedOuterStep ops sem y1 g) n next
      finishOuter k out
    rw [ClaimDotBoundedResult.bounded,ClaimDotBoundedResult.bounded]
    simp only [bind_assoc_eq]
    calc
      _ = (do let cf ← ownedOuterStep ops sem y1 g (iter,parts);outerPost k kont cf) := by
        apply bind_congr
        intro cf
        cases cf <;> rfl
      _ = (do let cf ← verifier.prepared_claim_loop.body ops inst sem (Array.to_slice y1) g k iter parts
              refOuterPost kont cf) := outer_step_cps ops inst sem y1 g k parts iter kont
      _ = _ := by
        apply bind_congr
        intro cf
        cases cf with
        | done out => rfl
        | cont next => exact ih next

theorem complete_outer_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (k parts : Parts) (iter : Range)
    (hend : iter.end.val=6) (hstart : iter.start.val≤6) :
    (do let out ← verifier.owned_claim_loops_loop0 ops iter sem.claims sem.extra sem.before_z1 y1 g parts
        finishOuter k out) =
      verifier.prepared_claim_loop ops inst iter sem (Array.to_slice y1) g k parts := by
  rw [owned_outer_loop_eq_bounded ops sem y1 g iter parts hend hstart]
  rw [bounded_outer_eq]
  have hf : refOuterStep ops inst sem y1 g k =
      ClaimDotBoundedResult.outerStep ops inst sem (Array.to_slice y1) g k := by
    funext s
    exact (ClaimDotBoundedResult.outerBody_eq_source ops inst sem (Array.to_slice y1) g k s.1 s.2).symm
  rw [hf,←ClaimDotBoundedResult.outerLoop_eq_source]
  symm
  exact ClaimDotBoundedResult.outerLoop_eq_bounded ops inst iter sem (Array.to_slice y1) g k parts hend hstart

/-- Whole emitted owned claim, on its complete semantic inputs, has the same
Result as the retained fission source. This discharges their nested-loop join,
not the separate native original/caller/P6 installation obligations. -/
theorem owned_claim_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (inactive kappa : E) (g : Array E 29#usize) :
    verifier.owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g kappa =
      verifier.prepared_claim ops inst sem (Array.to_slice y1) inactive g kappa := by
  unfold verifier.owned_claim_loops verifier.prepared_claim
  apply bind_congr
  intro k
  apply bind_congr
  intro parts
  calc
    _ = (do
      let out ← verifier.owned_claim_loops_loop0 ops {start:=0#usize,«end»:=6#usize}
        sem.claims sem.extra sem.before_z1 y1 g parts
      finishOuter k out) := by
              apply bind_congr
              rintro ⟨parts2,pending⟩
              cases pending <;> rfl
    _ = _ := complete_outer_eq ops inst sem y1 g k parts {start:=0#usize,«end»:=6#usize} (by decide) (by decide)

theorem complete_owner_eq {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 928#usize) (inactive kappa : E) (g : Array E 29#usize) :
    verifier.prepared_claim_owned ops inst sem y1 inactive g kappa =
      (do let result ← verifier.prepared_claim ops inst sem (Array.to_slice y1) inactive g kappa
          ok (result,sem)) := by
  unfold verifier.prepared_claim_owned
  rw [owned_claim_eq]

#print axioms owned_outer_cont_next
#print axioms owned_outer_progress
#print axioms owned_outer_loop_eq_bounded
#print axioms bounded_outer_eq
#print axioms complete_outer_eq
#print axioms owned_claim_eq
#print axioms complete_owner_eq
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
