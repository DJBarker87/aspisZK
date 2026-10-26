import FIp_InstalledLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_SemanticEquation
open Aeneas Aeneas.Std Result DrvC_Installation
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)

theorem assembled {C : Type} (err : C) (c : Configuration FIo_Install.W C) (r : NP6_StdModel.Reservation)
    (mask eta terminal extra product first running : MQ)
    (hm : Canon mask) (he : Canon eta) (ht : Canon terminal) (hx : Canon extra)
    (multiply : (FIp_Install.configuration err c r).boundaries.mul eta terminal=ok product)
    (initialAdd : (FIp_Install.configuration err c r).boundaries.add mask product=ok first)
    (finalAdd : (FIp_Install.configuration err c r).boundaries.add first extra=ok running) :
    Canon running ∧ decode running=decode mask+decode eta*decode terminal+decode extra := by
  have p := FIp_InstalledLaws.semantic_mul err c r eta terminal product he ht multiply
  have a := FIp_InstalledLaws.semantic_add err c r mask product first hm p.1 initialAdd
  have b := FIp_InstalledLaws.semantic_add err c r first extra running a.1 hx finalAdd
  exact ⟨b.1,by rw [b.2,a.2,p.2]⟩

#print axioms assembled
end AspisR1.FIp_SemanticEquation
end
