import JFn_HashModelNonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_HashFrame
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- Size separation preserves all pre-existing transcript calls whose input
length differs from the three authentication inputs. It establishes only
finite-model compatibility, not concrete SHA256 realization. -/
theorem unchanged_by_length (background : Bytes → State) (input : Bytes)
    (hp : input.length≠57607) (hu : input.length≠1880) (hc : input.length≠1758) :
    JFn_HashModelNonvacuity.extension background input=background input := by
  apply JFn_HashModelNonvacuity.unchanged
  · intro h;exact hp ((congrArg List.length h).trans JFn_HashLengths.proof)
  · intro h;exact hu ((congrArg List.length h).trans JFn_HashLengths.publicInput)
  · intro h;exact hc ((congrArg List.length h).trans JFn_HashLengths.checksum)

theorem transcript33 (background : Bytes → State) (input : Bytes) (length : input.length=33) :
    JFn_HashModelNonvacuity.extension background input=background input := by
  apply unchanged_by_length
  all_goals omega

#print axioms unchanged_by_length
#print axioms transcript33
end AspisR1.JFn_HashFrame
end
