import MultiproofConeRef.Funs

set_option autoImplicit false
namespace AspisR1.MultiproofConeLevelIteration
open Aeneas Aeneas.Std Result MultiproofConeRef

/-- Structural semantics of the source height loop. Rejection retains the
level's exact partial scratch, and no later level is executed. -/
def iterate (step : reference.Scratch → Result reference.Level) :
    Nat → reference.Scratch → Result reference.Level
  | 0, s => ok (.Done s)
  | h+1, s => do
    let out ← step s
    match out with
    | .Stop stopped => ok (.Stop stopped)
    | .Done next => iterate step h next

/-- Exact full-Result identity with the pinned extracted reference, proved by
height induction, rather than unrolling a concrete height-18 term. -/
theorem levels_eq_iteration {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (height : U32) (bound : height.val≤18)
    (s : reference.Scratch) :
    reference.levels D hash s physical height =
      iterate (fun state => reference.level_rows D hash state physical 0#usize 0#usize) height.val s := by
  generalize hn : height.val=n at bound ⊢
  induction n generalizing height s with
  | zero =>
    have hz : height=0#u32 := UScalar.eq_of_val_eq hn
    subst height
    rw [reference.levels]
    rfl
  | succ n ih =>
    have hnz : height≠0#u32 := by intro h;subst height;simp at hn
    obtain ⟨pred,sub,predVal⟩ := WP.spec_imp_exists
      (UScalar.sub_spec (x:=height) (y:=1#u32) (by scalar_tac))
    have pv : pred.val=n := by scalar_tac
    rw [reference.levels]
    simp only [hnz,if_false,iterate]
    cases row : reference.level_rows D hash s physical 0#usize 0#usize with
    | fail error => rfl
    | div => rfl
    | ok level =>
      cases level with
      | Stop stopped => rfl
      | Done next =>
        simp only [bind_tc_ok,sub]
        exact ih pred next pv (by omega)

/-- The domain certified by the source level harness; the node slice has the
frozen maximum-slot bound, and each reached frontier remains nonempty. -/
def Domain (physical : Slice U8) (s : reference.Scratch) : Prop :=
  0<s.n.val ∧ s.n.val≤16 ∧ s.at.val≤physical.val.length

/-- Domain-restricted local certificates compose through every reached level.
The preservation premise concerns only successful levels, never rejection. -/
theorem iterate_congr_on (P : reference.Scratch → Prop)
    (source target : reference.Scratch → Result reference.Level)
    (step : ∀ s, P s → source s=target s)
    (preserve : ∀ s, P s → ∀ next, source s=ok (.Done next) → P next)
    (h : Nat) (s : reference.Scratch) (domain : P s) :
    iterate source h s=iterate target h s := by
  induction h generalizing s with
  | zero => rfl
  | succ h ih =>
    simp only [iterate,←step s domain]
    cases eqout : source s with
    | fail error => rfl
    | div => rfl
    | ok out =>
      cases out with
      | Stop stopped => rfl
      | Done next =>
        simp only [bind_tc_ok]
        exact ih next (preserve s domain next eqout)

/-- The named one-level P6 source equation and preservation certificate are
explicit. This theorem neither asserts them for an arbitrary source nor
converts a Kani receipt into a kernel proof. The source/model caller is absent. -/
theorem adopt_eighteen {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (slotBound : physical.val.length≤5504)
    (source : reference.Scratch → Result reference.Level)
    (level_certificate : ∀ state, Domain physical state → source state=
      reference.level_rows D hash state physical 0#usize 0#usize)
    (preserve : ∀ state, Domain physical state → ∀ next,
      source state=ok (.Done next) → Domain physical next)
    (s : reference.Scratch) (domain : Domain physical s) :
    iterate source 18 s=reference.levels D hash s physical 18#u32 := by
  rw [levels_eq_iteration D hash physical 18#u32 (by decide) s]
  exact iterate_congr_on (Domain physical) source _ level_certificate preserve 18 s domain

#print axioms levels_eq_iteration
#print axioms iterate_congr_on
#print axioms adopt_eighteen
end AspisR1.MultiproofConeLevelIteration
