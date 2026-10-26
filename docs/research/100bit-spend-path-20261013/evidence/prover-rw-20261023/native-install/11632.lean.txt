import R1Z.ProverCommitPublicNonce40
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwNativeCaseCoverage
open ProverCommitPublicNonce40
attribute [local instance] Classical.propDecidable

/-- The native harness leaves one half arbitrary and sets the other to zero.
This is a surjective case parameterization, never a probability carrier. -/
def forceBad (half : Fin 2) (raw : Raw) : Raw := Function.update raw half 0

theorem rejected_cover (raw : Raw) (bad : decode raw = none) :
    ∃ half : Fin 2, forceBad half raw = raw := by
  have no_good : ¬ ∀ i, raw i ≠ 0 := by
    intro good
    simp only [decode,dif_pos good] at bad
    cases bad
  obtain ⟨half,h⟩ := Classical.not_forall.mp no_good
  have zero : raw half = 0 := by simpa using h
  refine ⟨half,?_⟩
  funext i
  by_cases hi : i=half
  · subst i
    simp only [forceBad,Function.update_self,zero]
  · simp only [forceBad,Function.update_of_ne hi]

theorem forced_rejected (half : Fin 2) (raw : Raw) :
    decode (forceBad half raw) = none := by
  have bad : ¬ ∀ i, forceBad half raw i ≠ 0 := by
    intro good
    exact good half (by simp only [forceBad,Function.update_self])
  simp only [decode,dif_neg bad]

def forcePrefix (choices : Nat → Fin 2) (tape : Nat → Raw) (stop : Nat) : Nat → Raw :=
  fun i => if i<stop then forceBad (choices i) (tape i) else tape i

theorem prefix_cover (tape : Nat → Raw) (stop : Nat)
    (bad : ∀ i, i<stop → decode (tape i) = none) :
    ∃ choices : Nat → Fin 2, forcePrefix choices tape stop = tape := by
  let choices : Nat → Fin 2 := fun i =>
    if hi : i<stop then Classical.choose (rejected_cover (tape i) (bad i hi)) else 0
  refine ⟨choices,?_⟩
  funext i
  by_cases hi : i<stop
  · simp only [forcePrefix,hi,if_true,choices,dif_pos hi]
    exact Classical.choose_spec (rejected_cover (tape i) (bad i hi))
  · simp only [forcePrefix,hi,if_false]

#print axioms rejected_cover
#print axioms forced_rejected
#print axioms prefix_cover
end R1Z.ProverRwNativeCaseCoverage
