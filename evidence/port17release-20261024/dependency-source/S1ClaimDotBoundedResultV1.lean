import CurrentClaimScalarChain
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimDotBoundedResult

/-- Fuel is an analysis device, not a new source limit. The instance below
proves fuel exhaustion unreachable using the source range cursor. -/
def bounded {S T : Type} (step : S → Result (ControlFlow S T)) : Nat → S → Result T
  | 0, _ => .div
  | n+1, s => do
    let cf ← step s
    match cf with
    | .done out => .ok out
    | .cont next => bounded step n next

theorem loop_eq_bounded {S T : Type}
    (step : S → Result (ControlFlow S T)) (P : S → Prop) (budget : S → Nat)
    (positive : ∀ s, P s → 0 < budget s)
    (progress : ∀ s next, P s → step s=.ok (.cont next) →
      P next ∧ budget next+1=budget s) :
    ∀ n s, P s → budget s=n → Aeneas.Std.loop step s=bounded step n s := by
  intro n
  induction n with
  | zero =>
    intro s hp hn
    have hpos := positive s hp
    omega
  | succ n ih =>
    intro s hp hn
    rw [Aeneas.Std.loop.eq_def]
    simp only [bounded]
    cases hs : step s with
    | fail e => simp only [hs,bind_tc_fail]
    | div => simp only [hs,bind_tc_div]
    | ok cf =>
      cases cf with
      | done out => simp only [hs,bind_tc_ok]
      | cont next =>
        simp only [hs,bind_tc_ok]
        obtain ⟨hpnext,hbudget⟩ := progress s next hp hs
        exact ih next hpnext (by omega)

abbrev State (D H : Type) :=
  ClaimScalar.Range × r1_semantic.Verified H × Usize × D

def step {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (y1 : Slice U8) (g : Array aspis_core.field.WideExact 29#usize) (s : State D H) :=
  verifier.prepared_claim_dot_loop.body ops inst y1 g s.1 s.2.1 s.2.2.1 s.2.2.2

def invariant {D H : Type} (s : State D H) : Prop :=
  s.1.end.val=29 ∧ s.1.start.val≤29

def budget {D H : Type} (s : State D H) : Nat := 30-s.1.start.val

/-- Actual emitted loop-body continuation forces the cursor to advance by one.
No read, push, scalar-canonicality or successful-whole-loop premise is added. -/
theorem step_progress {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (y1 : Slice U8) (g : Array aspis_core.field.WideExact 29#usize)
    (s next : State D H) (hp : invariant s)
    (h : step ops inst y1 g s=.ok (.cont next)) :
    invariant next ∧ budget next+1=budget s := by
  rcases s with ⟨iter,sem,point,dot⟩
  rcases next with ⟨iter',sem',point',dot'⟩
  obtain ⟨hsem,hpoint,l,scalar,coeff,hnext,hread,hweight,hpush⟩ :=
    ClaimScalar.body_cont ops inst sem sem' y1 g iter iter' point point' dot dot' h
  obtain ⟨hl,hactive,hstart,hend⟩ := ClaimTrace.next_some_step iter iter' l hnext
  dsimp [invariant,budget] at hp ⊢
  constructor
  · constructor
    · rw [hend];exact hp.1
    · omega
  · omega

/-- COMPLETE Result equality: all source errors, Rust Err values and child
failure/divergence are retained. Only the range control is bounded; arbitrary
children are not asserted total. At most29 active iterations plus finish. -/
theorem source_loop_eq_bounded {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (iter : ClaimScalar.Range)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize) (point : Usize) (dot : D)
    (hend : iter.end.val=29) (hstart : iter.start.val≤29) :
    verifier.prepared_claim_dot_loop ops inst iter sem y1 g point dot =
      bounded (step ops inst y1 g) (30-iter.start.val) (iter,sem,point,dot) := by
  apply loop_eq_bounded (step ops inst y1 g) invariant budget
  · intro s hp
    dsimp [invariant,budget] at hp ⊢
    omega
  · exact step_progress ops inst y1 g
  · exact ⟨hend,hstart⟩
  · rfl

def dot {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array aspis_core.field.WideExact 29#usize) (point : Usize) := do
  let initial ← ops.newDot
  bounded (step ops inst y1 g) 30
    ({start:=0#usize,«end»:=29#usize},sem,point,initial)

/-- The enclosing source helper has exactly the same complete Result under
this finite control interpretation, without any child-success premises. -/
theorem source_dot_eq_bounded {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array aspis_core.field.WideExact 29#usize) (point : Usize) :
    verifier.prepared_claim_dot ops inst sem y1 g point=dot ops inst sem y1 g point := by
  unfold verifier.prepared_claim_dot dot
  apply bind_congr
  intro initial
  exact source_loop_eq_bounded ops inst {start:=0#usize,«end»:=29#usize}
    sem y1 g point initial (by decide) (by decide)

#print axioms step_progress
#print axioms source_loop_eq_bounded
#print axioms source_dot_eq_bounded
end AspisR1CurrentPreparedClaim.ClaimDotBoundedResult
