import R1Z.PV_DL_EncoderBasis
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDCD4_Double194
set_option autoImplicit false

theorem binding {E : Type} (inst : aspis_core.r0.scalar.CodeField E) (x : E) :
    PV_DL_EncoderBasis.factor inst x=(do
      let square ← inst.mul x x
      let doubled ← inst.add square square
      let one ← inst.ONE
      inst.sub doubled one) := rfl

#print axioms binding
end R1Z.PV_RDCD4_Double194
