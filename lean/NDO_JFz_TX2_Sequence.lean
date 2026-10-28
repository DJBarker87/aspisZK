import NDO_JFz_TX2_AccumulateStep
set_option autoImplicit false
namespace AspisR1.JFz_TX2_Sequence
open Aeneas Aeneas.Std Result

def run {A : Type} (step : Nat → A → Result A) (initial : A) : Nat → Result A
  | 0 => ok initial
  | n+1 => do let state ← run step initial n;step n state

theorem source {A : Type} (step : Nat → A → Result A) (initial : A)
    (I : Nat → A → Prop) (bound : Nat) (start : I 0 initial)
    (advance : ∀ n, n<bound → ∀ state, I n state → ∃ out,step n state=ok out ∧ I (n+1) out)
    (n : Nat) (hn : n≤bound) : ∃ out,run step initial n=ok out ∧ I n out := by
  induction n with
  | zero => exact ⟨initial,rfl,start⟩
  | succ n ih =>
    obtain ⟨state,hr,hi⟩ := ih (by omega)
    obtain ⟨out,hs,ho⟩ := advance n (by omega) state hi
    exact ⟨out,by rw [run,hr,bind_tc_ok,hs],ho⟩
#print axioms source
end AspisR1.JFz_TX2_Sequence
