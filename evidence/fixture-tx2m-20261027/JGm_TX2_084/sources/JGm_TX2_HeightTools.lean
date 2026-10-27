import MultiproofConeLevelIteration
set_option autoImplicit false
namespace AspisR1.JGm_TX2_HeightTools
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem compose (step : reference.Scratch → Result reference.Level) (height : Nat)
    (V : Nat → reference.Scratch → Prop)
    (go : ∀ k, k<height → ∀ s, V k s → ∃ t, step s=ok (.Done t) ∧ V (k+1) t)
    (s : reference.Scratch) (initial : V 0 s) :
    ∃ out, MultiproofConeLevelIteration.iterate step height s=ok (.Done out) ∧ V height out := by
  induction height generalizing V s with
  | zero => exact ⟨s,rfl,initial⟩
  | succ h ih =>
    obtain ⟨next,run,view⟩ := go 0 (by omega) s initial
    obtain ⟨out,tail,last⟩ := ih (fun k s => V (k+1) s)
      (by intro k hk s vs;exact go (k+1) (by omega) s vs) next view
    refine ⟨out,?_,last⟩
    rw [MultiproofConeLevelIteration.iterate,run]
    exact tail
#print axioms compose
end AspisR1.JGm_TX2_HeightTools
