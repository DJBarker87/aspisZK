import R1Z.PV_RW_SamplerArrayLegacy
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RW_SamplerArrayBound
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1.SamplerMachineBounds
abbrev body := PV_RW_SamplerArraySource.iterator_body
abbrev execute := PV_RW_SamplerArraySource.iterator_loop

def finite : Nat → Array U32 8#usize → U64 → Usize → Result ((Array U32 8#usize) × U64)
  | 0, _, _, _ => .div
  | fuel+1, rank, remainder, j => do
    let flow ← body rank remainder j
    match flow with
    | .done out => ok out
    | .cont (nextRank,nextRemainder,nextIndex) => finite fuel nextRank nextRemainder nextIndex

theorem unfold_loop (rank : Array U32 8#usize) (remainder : U64) (j : Usize) :
    execute rank remainder j = (do
      let flow ← body rank remainder j
      match flow with
      | .done out => ok out
      | .cont (nextRank,nextRemainder,nextIndex) => execute nextRank nextRemainder nextIndex) := by
  unfold execute PV_RW_SamplerArraySource.iterator_loop
  rw [R1Z.ProverRwSuccessPowerTotal.loop_bind]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  intro flow _
  cases flow with
  | done out => rfl
  | cont next => rcases next with ⟨rank,remainder,j⟩; rfl

theorem sufficient (rank : Array U32 8#usize) (remainder : U64) (j : Usize)
    (hr : remainder.val < P) (bound : j.val ≤ 8) :
    execute rank remainder j = finite (j.val+1) rank remainder j := by
  generalize index : j.val = n
  induction n generalizing rank remainder j with
  | zero =>
    have stop : ¬ j > 0#usize := by change ¬ 0 < j.val; omega
    rw [unfold_loop]
    simp only [finite,body,PV_RW_SamplerArraySource.iterator_body,stop,if_false,bind_tc_ok]
  | succ n ih =>
    obtain ⟨nextIndex,quotient,nextRemainder,hs,hj,hr1⟩ :=
      PV_RW_SamplerArrayLegacy.step_invariant rank remainder j hr (by omega) bound
    have index1 : nextIndex.val = n := by omega
    rw [unfold_loop]
    simp only [finite,hs,bind_tc_ok]
    exact ih (rank.set nextIndex quotient) nextRemainder nextIndex hr1 (by omega) index1

theorem arity8 (rank : Array U32 8#usize) :
    execute rank 0#u64 8#usize = finite 9 rank 0#u64 8#usize := by
  exact sufficient rank 0#u64 8#usize P_pos (by change 8≤8; omega)

theorem harness_bound (j : Usize) (bound : j.val ≤ 8) : j.val+1 < 10 := by omega
#print axioms unfold_loop
#print axioms sufficient
#print axioms arity8
#print axioms harness_bound
end R1Z.PV_RW_SamplerArrayBound
