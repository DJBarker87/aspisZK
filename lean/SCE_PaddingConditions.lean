import SCE_AdaptivePadding
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_PaddingConditions
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment SCE_AdaptivePadding GExq_AccountExperiment

/-- Padding changes no response-selected second entry, data, slot or state. -/
theorem second_inputs {A : Type} (a : Adversary A) (address : Bytes)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (final : A) (H : Bytes → State) :
    (eval H ((pad a address).second i saved post final)).2 =
      (eval H (a.second i saved post final)).2 := rfl

/-- Every condition on the two selected native inputs is preserved. This
includes the current admission and game fields; no assertion of inhabiting
all installed cryptographic source premises is made. -/
theorem preserve {A : Type} (a : Adversary A) (address : Bytes)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (H : Bytes → State) (R : FirstInputs A → SecondInputs A → Prop) :
    R (eval H (pad a address).first).2
      (eval H ((pad a address).second (eval H (pad a address).first).2 saved post final)).2 ↔
    R (eval H a.first).2 (eval H (a.second (eval H a.first).2 saved post final)).2 := Iff.rfl

#print axioms second_inputs
#print axioms preserve
end AspisR1.SCE_PaddingConditions
end
