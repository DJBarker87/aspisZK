import R1Z.ProverCommitGammaFill53
/-! One gamma power array is shared by the entire 1024-cell batch. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitGammaOutput53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitWideOps48 ProverCommitMix48 ProverCommitGammaCell53
open scoped BigOperators

theorem all (c : Nat → Nat → Raw) (hc : ∀ l, l<29 → ∀ j, j<1024 → canonical (c l j))
    (p : Nat → Raw) (hp : ∀ l, l<29 → canonical (p l)) :
    ∃ out : Nat → Raw, gamma53.all (table c) (sourceArray 29#usize p)=ok (sourceArray 1024#usize out) ∧
      (∀ j, j<1024 → canonical (out j)) ∧
      ∀ j : Fin 1024, value (out j.val)=ProverCommitMix48.sum (fun l => c l j.val) p 29 0 := by
  obtain ⟨out,hout,hcout,hdout⟩ := ProverCommitGammaFill53.fill c hc p hp 1024
    (fun _ => ProverCommitGamma48.zero) (fun _ _ => ProverCommitGamma48.zero_canonical)
    0#usize 1024#u16 rfl (by decide)
  refine ⟨out,?_,hcout,?_⟩
  · rw [gamma53.all,ProverCommitGamma48.repeat_zero]
    exact hout
  · intro j
    rw [hdout j.val j.isLt,if_pos (by have := j.isLt;change 0≤j.val ∧ j.val<0+1024;omega)]

def run (c : Array (Array Source 1024#usize) 29#usize) (x : Source) :
    Result (Array Source 1024#usize) := do
  let p ← gamma x
  gamma53.all c p

theorem exact_result (c : Nat → Nat → Raw)
    (hc : ∀ l, l<29 → ∀ j, j<1024 → canonical (c l j)) (x : Raw) (hx : canonical x) :
    ∃ out : Nat → Raw, run (table c) (source x)=ok (sourceArray 1024#usize out) ∧
      (∀ j, j<1024 → canonical (out j)) ∧
      ∀ j : Fin 1024, value (out j.val)=∑ l : Fin 29, value x^l.val*value (c l.val j.val) := by
  obtain ⟨p,hp,hcp,hdp⟩ := ProverCommitGamma48.gamma_exact x hx
  obtain ⟨out,hout,hcout,hdout⟩ := all c hc p hcp
  refine ⟨out,?_,hcout,?_⟩
  · simp only [run,hp,hout,bind_tc_ok]
  · intro j
    rw [hdout j,ProverCommitBatchMix48.sum_powers (fun l => c l j.val) p (value x) hdp 29 0 (by decide)]
    simp only [Nat.zero_add]

#print axioms all
#print axioms exact_result
end R1Z.ProverCommitGammaOutput53
