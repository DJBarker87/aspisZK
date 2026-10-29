import R1Z.PV_RunJoin_ActualAlpha60
import R1Z.PV_RunJoin_ActualScalar60
import R1Z.PV_RunJoin_ActualCircle60
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualSample60
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open PV_RunJoin_ActualData59
variable [ExternalTypes] [ExternalFuns]

/-- Remaining source facts, explicitly separated from the stored-record
projection equalities already proved. No producer discharge is claimed. -/
structure SourceFacts (p : Phase) : Prop where
  alpha : ∀ i,i<10 → ProverCommitSubfieldOps47.Canonical ((data p).p i)
  x0 : ProverCommitSubfieldOps47.Canonical (data p).x0
  y0 : ProverCommitSubfieldOps47.Canonical (data p).y0
  x1 : ProverCommitSubfieldOps47.Canonical (data p).x1
  y1 : ProverCommitSubfieldOps47.Canonical (data p).y1
  gamma : ProverCommitWideOps48.canonical (data p).g
  kappa : ProverCommitWideOps48.canonical (data p).k
  alpha0 : ProverCommitWideOps48.canonical (data p).a
  alpha1 : ProverCommitWideOps48.canonical (data p).b
  circle0 : (PV_RunJoin_ActualCircle60.coordinates p 0).1^2+
    (PV_RunJoin_ActualCircle60.coordinates p 0).2^2=1
  circle1 : (PV_RunJoin_ActualCircle60.coordinates p 1).1^2+
    (PV_RunJoin_ActualCircle60.coordinates p 1).2^2=1

theorem association (p : Phase) (source : SourceFacts p) : PV_RunJoin_OpeningImages54.Sample (data p) := by
  obtain ⟨hx0,hy0,hx1,hy1⟩ := PV_RunJoin_ActualCircle60.stored p source.circle0 source.circle1
  obtain ⟨hg,hk,ha,hb⟩ := PV_RunJoin_ActualScalar60.openings p
  exact ⟨source.alpha,source.x0,source.y0,source.x1,source.y1,
    source.gamma,source.kappa,source.alpha0,source.alpha1,
    PV_RunJoin_ActualAlpha60.stored p,hx0,hy0,hx1,hy1,hg,hk,ha,hb⟩

#print axioms association
end R1Z.PV_RunJoin_ActualSample60
