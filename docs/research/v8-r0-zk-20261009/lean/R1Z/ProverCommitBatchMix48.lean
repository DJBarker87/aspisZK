import R1Z.ProverCommitGamma48
/-! Complete coefficient-cell producer: the native power owner is composed
with all 29 mix iterations. No gamma-power equality premise remains. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitBatchMix48
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48
open scoped BigOperators

theorem sum_powers (q p : Nat → Raw) (a : Exact)
    (hp : ∀ j, j < 29 → value (p j)=a^j) (n i : Nat) (bound : i+n ≤ 29) :
    ProverCommitMix48.sum q p n i=∑ j : Fin n, a^(i+j.val)*value (q (i+j.val)) := by
  induction n generalizing i with
  | zero => simp only [ProverCommitMix48.sum,Fin.sum_univ_zero]
  | succ n ih =>
    rw [ProverCommitMix48.sum,hp i (by omega),ih (i+1) (by omega)]
    simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Nat.add_zero,
      Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

def run (q : Array Source 29#usize) (x : Source) : Result Source := do
  let gp ← gamma x
  mix q gp 0#usize 29#u8 field.wide_exact.WideExact.ZERO

theorem value_exact (q : Nat → Raw) (hq : ∀ j, j < 29 → canonical (q j))
    (x : Raw) (hx : canonical x) :
    ∃ z : Raw, run (sourceArray 29#usize q) (source x)=ok (source z) ∧
      canonical z ∧ value z=∑ j : Fin 29, (value x)^j.val*value (q j.val) := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitGamma48.gamma_exact x hx
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitMix48.owner_value q p hq hcp
    ProverCommitGamma48.zero ProverCommitGamma48.zero_canonical
  refine ⟨z,?_,hcz,?_⟩
  · simp only [run,hp,ProverCommitGamma48.source_zero,bind_tc_ok,hz]
  · rw [hdz,ProverCommitGamma48.zero_value,zero_add,sum_powers q p (value x) hdp 29 0 (by omega)]
    simp only [Nat.zero_add]

#print axioms sum_powers
#print axioms value_exact
end R1Z.ProverCommitBatchMix48
