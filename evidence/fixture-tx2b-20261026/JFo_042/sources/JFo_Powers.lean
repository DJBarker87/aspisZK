import JFo_GammaCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Powers
open Aeneas Aeneas.Std Result

theorem source : ∃ out : Array Tx2N_Powers.E 29#usize, Tx2N_Powers.powers 29#usize JFo_Prepared.value.gamma=ok out ∧
    ∀ j : Fin 29,
      AspisR1LoopPowers.Canonical (Tx2N_Powers.toPowers (out.val[j.val]'(by rw [out.property];exact j.isLt))) ∧
      AspisR1LoopPowers.decode (Tx2N_Powers.toPowers (out.val[j.val]'(by rw [out.property];exact j.isLt))) =
        AspisR1LoopPowers.decode (Tx2N_Powers.toPowers JFo_Prepared.value.gamma)^j.val :=
  Tx2N_Powers.total_exact 29#usize JFo_Prepared.value.gamma JFo_GammaCanonical.source

#print axioms source
end AspisR1.JFo_Powers
end
