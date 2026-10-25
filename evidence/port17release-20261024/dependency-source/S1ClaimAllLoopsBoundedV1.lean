import S1ClaimBoundedResultCompositionV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimDotBoundedResult
abbrev OuterState := ClaimScalar.Range × Array aspis_core.field.WideExact 7#usize

def outerStep {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize)
    (k : Array aspis_core.field.WideExact 7#usize) (s : OuterState) :=
  outerBody ops inst sem y1 g k s.1 s.2

def outerInvariant (s : OuterState) : Prop := s.1.end.val=6 ∧ s.1.start.val≤6

def outerBudget (s : OuterState) : Nat := 7-s.1.start.val

theorem outer_step_progress {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize)
    (k : Array aspis_core.field.WideExact 7#usize) (s next : OuterState)
    (hp : outerInvariant s) (h : outerStep ops inst sem y1 g k s=.ok (.cont next)) :
    outerInvariant next ∧ outerBudget next+1=outerBudget s := by
  rcases s with ⟨iter,parts⟩
  rcases next with ⟨iter',parts'⟩
  unfold outerStep at h
  rw [outerBody_eq_source] at h
  obtain ⟨point,i,value,hnext,hdot,hinc,hupdate⟩ :=
    ClaimTrace.body_cont ops inst sem y1 g k parts parts' iter iter' h
  obtain ⟨hl,hactive,hstart,hend⟩ := ClaimTrace.next_some_step iter iter' point hnext
  dsimp [outerInvariant,outerBudget] at hp ⊢
  constructor
  · constructor
    · rw [hend];exact hp.1
    · omega
  · omega

theorem outerLoop_eq_bounded {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (iter : ClaimScalar.Range)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize)
    (k parts : Array aspis_core.field.WideExact 7#usize)
    (hend : iter.end.val=6) (hstart : iter.start.val≤6) :
    outerLoop ops inst iter sem y1 g k parts =
      bounded (outerStep ops inst sem y1 g k) (7-iter.start.val) (iter,parts) := by
  apply loop_eq_bounded (outerStep ops inst sem y1 g k) outerInvariant outerBudget
  · intro s hp
    dsimp [outerInvariant,outerBudget] at hp ⊢
    omega
  · exact outer_step_progress ops inst sem y1 g k
  · exact ⟨hend,hstart⟩
  · rfl

/-- Both levels of source claim control are finite. All actual scalar, push,
finish, powers and weighted-sum operations remain in their original order. -/
def allBoundedClaim {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : aspis_core.field.WideExact)
    (g : Array aspis_core.field.WideExact 29#usize) (kappa : aspis_core.field.WideExact) := do
  let k ← ops.powers 7#usize kappa
  let initial := Array.repeat 7#usize aspis_core.field.WideExact.ZERO
  let parts ← Array.update initial 0#usize inactive
  bounded (outerStep ops inst sem y1 g k) 7
    ({start:=0#usize,«end»:=6#usize},parts)

/-- Complete enclosing extracted claim Result identity, with no success,
canonicality or total-child premises. Control exhaustion is unreachable;
explicit child failure/divergence remains possible and is preserved. This
source is the checked fission reference; original Rust equivalence is open. -/
theorem allBoundedClaim_eq_source {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (inactive : aspis_core.field.WideExact)
    (g : Array aspis_core.field.WideExact 29#usize) (kappa : aspis_core.field.WideExact) :
    allBoundedClaim ops inst sem y1 inactive g kappa =
      verifier.prepared_claim ops inst sem y1 inactive g kappa := by
  unfold allBoundedClaim verifier.prepared_claim
  repeat' (apply bind_congr;intro x)
  rw [←outerLoop_eq_source]
  symm
  exact outerLoop_eq_bounded ops inst {start:=0#usize,«end»:=6#usize}
    sem y1 g _ _ (by decide) (by decide)

#print axioms outer_step_progress
#print axioms outerLoop_eq_bounded
#print axioms allBoundedClaim_eq_source
end AspisR1CurrentPreparedClaim.ClaimDotBoundedResult
