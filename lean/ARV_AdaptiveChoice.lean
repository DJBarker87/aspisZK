import ARV_Adaptive
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_AdaptiveChoice
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw GExq_AccountExperiment SCE_Experiment
attribute [local instance] Classical.propDecidable

theorem exact {A : Type} (i : FirstInputs A) (j : SecondInputs A)
    (address : Bytes) (original : State) (H : Bytes → State)
    (input : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A) :
    eval H ((ARV_Adaptive.adversary i j address original).second input saved post final) =
      ([(address,H address)],if H address = original then j else ARV_Constant.poison j) := by
  by_cases h : H address = original
  · simp only [ARV_Adaptive.adversary,eval,if_pos h]
  · simp only [ARV_Adaptive.adversary,eval,if_neg h]

#print axioms exact
end AspisR1.ARV_AdaptiveChoice
end
