import F3S_FinishUnique
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3S_PrimitiveNonvacuity
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1Stage2.Stage2Finish
/-- Exact actual primitive observations are inhabited and unique on this
accepted finish. This does not inhabit the remaining owner leaves, the
complete native accepted pair, or a collision-free complete carrier join. -/
 theorem accepted {W : Type} (ops : FinishOps W) (v : verifier.View) (p : verifier.Prepared)
    (a : verifier.Accumulator) (s2 : p.variant=.S2)
    (success : Port4D_FinishInstall.finish ops v p a none=ok (.Ok ())) :
    ∃! x : F3S_FinishWitness.Primitives ops v p a, True := by
  obtain ⟨x⟩ := F3S_FinishWitness.source ops v p a s2 success
  exact ⟨x,trivial,fun y _=>F3S_FinishUnique.unique ops v p a y x⟩
#print axioms accepted
end AspisR1.F3S_PrimitiveNonvacuity
end
