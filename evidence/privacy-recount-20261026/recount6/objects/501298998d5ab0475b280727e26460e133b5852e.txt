import R1Z.ProverRwRngCallerStep
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngCallerReplay
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
open ProverRwRngCallerControl ProverRwRngCallerStep
variable [NativeTypes] [ErasureFns]
abbrev State (N L B : Type) := Tape × N × L × B × Usize
abbrev Output (N L B : Type) := Tape × N × L × B × core.result.Result RetriedProof ProverRwRngCaller.Error

def step {N L B : Type} (policy : Policy N) (body : Body B L) (s : State N L B) :=
  retry_step policy body s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2

def run {N L B : Type} (policy : Policy N) (body : Body B L) (s : State N L B) :=
  retry_attempt policy body s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2

inductive Replay {N L B : Type} (policy : Policy N) (body : Body B L) :
    State N L B → List (State N L B) → Output N L B → Prop where
  | done {s out} : step policy body s = .ok (.done out) → Replay policy body s [s] out
  | cont {s next states out} : step policy body s = .ok (.cont next) →
      Replay policy body next states out → Replay policy body s (s::states) out

theorem run_factor {N L B : Type} (policy : Policy N) (body : Body B L) (s : State N L B) :
    run policy body s = (do
      let flow ← step policy body s
      match flow with | .done out => .ok out | .cont next => run policy body next) := by
  rcases s with ⟨p,n,l,b,k⟩
  unfold run step
  rw [retry_factor]
  apply (bind_eq_iff _ _ _).mpr
  intro flow h
  cases flow with
  | done out => rfl
  | cont next => rcases next with ⟨p',n',l',b',k'⟩; rfl

theorem replay_sound {N L B : Type} {policy : Policy N} {body : Body B L}
    {s : State N L B} {states out} (path : Replay policy body s states out) :
    run policy body s = .ok out := by
  induction path with
  | done h => rw [run_factor,h]; rfl
  | cont h path ih => rw [run_factor,h]; exact ih

theorem replay_complete {N L B : Type} (policy : Policy N) (body : Body B L)
    (s : State N L B) (out : Output N L B) (hrun : run policy body s = .ok out) :
    ∃ states, Replay policy body s states out := by
  suffices ∀ fuel s, 9 - s.2.2.2.2.val = fuel → run policy body s = .ok out →
      ∃ states, Replay policy body s states out by exact this _ s rfl hrun
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro s hf hr
    rw [run_factor] at hr
    cases hs : step policy body s with
    | fail e => simp only [hs,bind_tc_fail] at hr; cases hr
    | div => simp only [hs,bind_tc_div] at hr; cases hr
    | ok flow =>
      rw [hs] at hr
      cases flow with
      | done result =>
        have eq : result = out := by exact Result.ok.inj hr
        subst result
        exact ⟨[s],.done hs⟩
      | cont next =>
        have prog := step_progress policy body s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 next hs
        have less : 9 - next.2.2.2.2.val < fuel := by omega
        obtain ⟨states,path⟩ := ih _ less next rfl hr
        exact ⟨s::states,.cont hs path⟩

def callbacks {N L B : Type} : List (State N L B) → Nat
  | [] => 0
  | s::ss => (if s.2.2.2.2.val < 8 then 1 else 0) + callbacks ss

theorem callback_bound {N L B : Type} {policy : Policy N} {body : Body B L}
    {s : State N L B} {states out} (path : Replay policy body s states out)
    (start : s.2.2.2.2.val ≤ 8) : callbacks states ≤ 8 - s.2.2.2.2.val := by
  induction path with
  | done h => simp only [callbacks]; split <;> omega
  | @cont s next states out h path ih =>
    have prog := step_progress policy body s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 next h
    have nextBound : next.2.2.2.2.val ≤ 8 := by omega
    have bounded := ih nextBound
    simp only [callbacks,if_pos prog.1]
    omega

theorem cap8 {N L B : Type} (policy : Policy N) (body : Body B L)
    (p : Tape) (n : N) (l : L) (b : B) (out : Output N L B)
    (admitted : prove_masked_retrying_with policy body true p n l b = .ok out) :
    ∃ states, Replay policy body (p,n,l,b,0#usize) states out ∧ callbacks states ≤ 8 := by
  have hr : run policy body (p,n,l,b,0#usize) = .ok out := admitted
  obtain ⟨states,path⟩ := replay_complete policy body _ out hr
  exact ⟨states,path,callback_bound path (by change (0#usize).val ≤ 8; decide)⟩

#print axioms run_factor
#print axioms replay_sound
#print axioms replay_complete
#print axioms callback_bound
#print axioms cap8
end R1Z.ProverRwRngCallerReplay
