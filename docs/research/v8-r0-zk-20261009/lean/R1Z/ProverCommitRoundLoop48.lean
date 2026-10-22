import R1Z.ProverCommitRoundStep48
/-! Complete finite composition of native batched-round transitions. The term
sum includes the exact source permutation; no concrete 4096-step term reduces. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitRoundLoop48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48
abbrev Triple := Usize × Usize × Usize

def legal (u : Triple) : Prop := u.1.val < 256 ∧ u.2.1.val < 4 ∧ u.2.2.val < 4

def loop (q w : Array Source 1024#usize) : List Triple → Array Source 7#usize → Result (Array Source 7#usize)
 | [],out => ok out
 | u::us,out => do
   let next ← round_step q w out u.1 u.2.1 u.2.2
   loop q w us next

def terms (q w : Nat → Raw) : List Triple → Nat → Exact
 | [],_ => 0
 | u::us,k =>
   (if k=u.2.1.val+ProverCommitRoundStep48.perm u.2.2.val then
      value (q (4*u.1.val+u.2.1.val))*value (w (4*u.1.val+u.2.2.val)) else 0)+terms q w us k

attribute [local irreducible] sourceArray source value terms

theorem loop_value (q w : Nat → Raw) (hq : ∀ k, k < 1024 → canonical (q k))
    (hw : ∀ k, k < 1024 → canonical (w k)) (us : List Triple) (hus : ∀ u ∈ us, legal u)
    (xs : Nat → Raw) (hxs : ∀ k, k < 7 → canonical (xs k)) :
    ∃ ys : Nat → Raw,
      loop (sourceArray 1024#usize q) (sourceArray 1024#usize w) us (sourceArray 7#usize xs)=
        ok (sourceArray 7#usize ys) ∧ (∀ k, k < 7 → canonical (ys k)) ∧
      ∀ k, k < 7 → value (ys k)=value (xs k)+terms q w us k := by
  induction us generalizing xs with
  | nil =>
    refine ⟨xs,rfl,hxs,?_⟩
    intro k hk
    rw [terms,add_zero]
  | cons u us ih =>
    have hu := hus u (by simp only [List.mem_cons_self])
    obtain ⟨next,hnext,hcnext,hdnext⟩ := ProverCommitRoundStep48.step q w xs hq hw hxs
      u.1 u.2.1 u.2.2 hu.1 hu.2.1 hu.2.2
    obtain ⟨ys,hy,hcy,hdy⟩ := ih (fun v hv => hus v (List.mem_cons_of_mem u hv)) next hcnext
    refine ⟨ys,?_,hcy,?_⟩
    · simp only [loop,hnext,bind_tc_ok,hy]
    · intro k hk
      rw [hdy k hk,hdnext k hk,terms]
      exact add_assoc _ _ _

#print axioms loop_value
end R1Z.ProverCommitRoundLoop48
