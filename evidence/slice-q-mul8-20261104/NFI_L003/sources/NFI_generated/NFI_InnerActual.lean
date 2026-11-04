import NFI_InnerTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFI_InnerActual
open Aeneas Aeneas.Std Result NFI_InnerCut

theorem emitted (oracle : NFF_LoggedEight.Oracle) (law : NFF_LoggedEight.Law oracle)
    (fuel : Nat) (before : Cut) (domain : NEV_DotInputs.Canonical before.input.g)
    (n : Nat) (width : n+fuel≤4)
    (span : before.iter.start.val+fuel=before.iter.end.val)
    (endpoint : before.iter.end.val≤26)
    (invariant : NFE_NEV_DotSweep.Sweep n 0 before.sums) :
    (NFI_InnerTrace.run oracle fuel before).1 = NFI_InnerTrace.pack before.input
      (FIp_NativeDots.fast_dots.four_dots_one_loop0_loop0 before.iter
        before.input.q before.input.g before.input.slot before.sums) := by
  rw [NFI_InnerTrace.replay,NFF_LoggedLoop.replay oracle law before.input.q
    before.input.g domain before.input.slot fuel before.iter before.sums
    n width span endpoint invariant]

theorem borrowed_frame (oracle : NFF_LoggedEight.Oracle) (fuel : Nat) (before : Cut)
    (visited : Cut) (member : visited∈(NFI_InnerTrace.run oracle fuel before).2) :
    visited.input.q=before.input.q ∧ visited.input.g=before.input.g ∧
    visited.input.slot=before.input.slot ∧ visited.input.qPlace=before.input.qPlace ∧
    visited.input.gPlace=before.input.gPlace := by
  have h := NFI_InnerTrace.frames oracle fuel before visited member
  exact ⟨congrArg Input.q h,congrArg Input.g h,congrArg Input.slot h,
    congrArg Input.qPlace h,congrArg Input.gPlace h⟩

theorem canonical_at_cut (oracle : NFF_LoggedEight.Oracle) (fuel : Nat) (before : Cut)
    (domain : NEV_DotInputs.Canonical before.input.g)
    (visited : Cut) (member : visited∈(NFI_InnerTrace.run oracle fuel before).2) :
    NEV_DotInputs.Canonical visited.input.g := by
  rw [(borrowed_frame oracle fuel before visited member).2.1]
  exact domain

#print axioms emitted
#print axioms borrowed_frame
#print axioms canonical_at_cut
end AspisR1.NFI_InnerActual
end
