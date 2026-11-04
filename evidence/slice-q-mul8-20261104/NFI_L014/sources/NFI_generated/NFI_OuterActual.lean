import NFI_OuterTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_OuterActual
open Aeneas Aeneas.Std Result NFI_OuterCut

theorem emitted (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (fuel : Nat) (before : Cut) (domain : NEV_DotInputs.Canonical before.input.g)
    (n : Nat) (remaining : n+fuel=7)
    (stride : before.iter.step_by.val=4) (finish : before.iter.iter.end.val=26)
    (start : before.iter.iter.start.val=min (4*n) 26)
    (bound : NFE_NFA_FoldEight.Bound before.limbs n) :
    (NFI_OuterTrace.run oracle fuel before).1 = NFI_OuterTrace.pack before.input
      (FIp_NativeDots.fast_dots.four_dots_one_loop0 before.iter
        before.input.q before.input.g before.input.slot before.limbs) := by
  rw [NFI_OuterTrace.replay]
  congr 1
  exact NFF_LoggedOuterLoop.replay oracle law before.input.q before.input.g
    domain before.input.slot fuel before.iter before.limbs n remaining stride finish start bound

#print axioms emitted
end AspisR1.NFI_OuterActual
end
