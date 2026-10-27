import F3L_RhoMeaning
import R4TransportCircleCoordinates
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3M_CircleSource
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

def qm (q : AspisR1CircleSampleWrapper.field.QM31) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def point (p : AspisR1CircleSampleWrapper.circle.SecureCirclePoint) : aspis_core.circle.SecureCirclePoint :=
  ⟨qm p.x,qm p.y⟩
def row : FinishModel.CircleRow → AspisR1CircleSampleWrapper.r0_transcript.CircleRow
  | .First => .First
  | .Second => .Second

def source (block : Array U8 32#usize) (r : FinishModel.CircleRow) :
    Result aspis_core.circle.SecureCirclePoint := do
  let p ← AspisR1CircleSampleWrapper.sampler.circle_sample block (row r)
  ok (point p)

def install (B : FinishModel.Boundaries) : FinishModel.Boundaries := {B with circle:=source}

theorem coordinates (p : AspisR1CircleSampleWrapper.circle.SecureCirclePoint) :
    (LiteralOpeningView.eK (F3L_RhoMeaning.decode (point p).x),
      LiteralOpeningView.eK (F3L_RhoMeaning.decode (point p).y))=
      AspisR1CircleSampleWrapper.R4TransportCircleCoordinates.coordinates p := by
  rfl

#print axioms coordinates
end AspisR1.F3M_CircleSource
end
