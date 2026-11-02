import NEI_DotReduction
import NEG_DotAssociation
set_option autoImplicit false
noncomputable section
namespace NEI_DotFinishAssociation
open Aeneas Aeneas.Std Result
abbrev D := NEI_DotFinishRaw.fast_pairing.canonical.Dot
def toD (x : D) : FIo_Native.fast_pairing.canonical.Dot := ⟨x.sums⟩
theorem limbs (x : NEI_DotFinishRaw.fast_pairing.canonical.Q) :
 NEI_DotFinishRaw.fast_pairing.canonical.Q.limbs x =
 FIo_Native.fast_pairing.canonical.Q.limbs x := by rfl
theorem finish (x : D) :
 NEI_DotFinishRaw.fast_pairing.canonical.Dot.finish x =
 FIo_Native.fast_pairing.canonical.Dot.finish (toD x) := by
 simp only [NEI_DotFinishRaw.fast_pairing.canonical.Dot.finish,
  FIo_Native.fast_pairing.canonical.Dot.finish,NEI_DotReduction.same,toD]
#print axioms limbs
#print axioms finish
end NEI_DotFinishAssociation
end
