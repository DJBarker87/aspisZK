import R1Z.ProverRwRngOwnerEmission
import R1Z.ProverRwRngControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerStep
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
variable [ErasureFns]
abbrev Status := ProverRwRngControl.Status

def mapResult {A B : Type} (f : A → B) (x : Result A) : Result B := do
  let a ← x
  .ok (f a)

theorem map_bind {A B C : Type} (f : B → C) (x : Result A) (k : A → Result B) :
    mapResult f (x >>= k) = (x >>= fun a => mapResult f (k a)) := by
  cases x <;> rfl

theorem draw_state (p : Tape) (input : Array U8 64#usize) :
    Tape.draw p input = mapResult (fun ((after,r),block) => (r,after,block))
      (Tape.Insts.Prover_rw_rng_preflightDraw64.fill p input) := by
  unfold Tape.draw Tape.Insts.Prover_rw_rng_preflightDraw64.fill
  simp only [mapResult, bind_assoc_eq, bind_tc_ok]
  apply (bind_eq_iff _ _ _).mpr
  intro u hu
  apply (bind_eq_iff _ _ _).mpr
  rintro ⟨block,status⟩ hentry
  change ((p.used + 1#usize) >>= fun next => .ok (status,{p with used := next},block)) =
    (((p.used + 1#usize) >>= fun next => .ok (({p with used := next},status),block)) >>=
      fun a => .ok (a.1.2,a.1.1,a.2))
  rw [bind_assoc_eq]
  rfl

def swapDone : ControlFlow (Tape × Usize) (Tape × Status) →
    ControlFlow (Tape × Usize) (Status × Tape)
  | .cont x => .cont x
  | .done (p,r) => .done (r,p)

theorem body_same (nonce : Array U8 32#usize) (limit retry : Usize) (p : Tape) :
    StateOnlyAttemptSecrets.old_loop.body nonce limit p retry =
      mapResult swapDone (StateOnlyAttemptSecrets.generate_with_loop.body
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce limit p retry) := by
  unfold StateOnlyAttemptSecrets.old_loop.body StateOnlyAttemptSecrets.generate_with_loop.body
  split
  · simp only [zeroize.Zeroizing.new,
      zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry,
      draw_state, map_bind, mapResult, bind_assoc_eq]
    apply (bind_eq_iff _ _ _).mpr
    rintro ⟨⟨after,status⟩,block⟩ hreply
    cases status <;> simp only [bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      StateOnlyAttemptEntropyError.Insts.CoreConvertFromU8,
      StateOnlyAttemptEntropyError.Insts.CoreConvertFromU8.from,swapDone]
    all_goals
      repeat' first
        | rfl
        | simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok,swapDone]
        | (apply (bind_eq_iff _ _ _).mpr; first | rintro ⟨x,y⟩ hx | intro x hx)
        | split
  · simp only [mapResult,bind_tc_ok,swapDone]

#print axioms map_bind
#print axioms draw_state
#print axioms body_same
end R1Z.ProverRwRngOwnerStep
