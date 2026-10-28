import R1Z.ProverRwP6PowersCoordinates
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BodyGamma
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverCommitWideOps48
variable [ExternalTypes]
theorem source (ops : ExternalFuns) (x : W) :
    (ProverRwP6BodyStore.selected ops).op254 29#usize x =
      ProverRwP6ResultMap.map (ProverRwP6ArrayMap.map fromW)
        (AspisR1ProducerRelease47.gamma (toW x)) := ProverRwP6PowersGammaSource.gamma ops x

theorem values (ops : ExternalFuns) (x : Raw) (hx : canonical x) :
    ∃ out, (ProverRwP6BodyStore.selected ops).op254 29#usize (fromW (ProverCommitWideOps48.source x)) = ok out ∧
      ∀ i : Usize, i.val<29 → ∃ cell, Array.index_usize out i = ok cell ∧
        ProverRwP6WideDecode.canonical cell ∧ ProverRwP6WideDecode.decode cell = value x^i.val :=
  ProverRwP6PowersCoordinates.gamma ops x hx
#print axioms source
#print axioms values
end R1Z.ProverRwP6BodyGamma
