import JFr_RealRounds
set_option autoImplicit false
namespace AspisR1.JFr_BoundaryComparison
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem same (x : MainQM) : core.cmp.PartialEq.ne.trait_default
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 x x=ok false := by
  rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩
  simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]

theorem checked (r : Fin 10) :
    (do let boundary ← generatedMainBoundary (JFr_RealRounds.polynomial r)
        core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
          boundary (JFr_RealRounds.running r))=ok false := by
  rw [JFr_RealRounds.boundary r,bind_tc_ok]
  exact same _

#print axioms same
#print axioms checked
end AspisR1.JFr_BoundaryComparison
