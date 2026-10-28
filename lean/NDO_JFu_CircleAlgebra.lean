import RPz7_F3M_CircleSourceCall
import RPx_FIr_FinishComparison
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFu_CircleAlgebra
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureProductCorrectness
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerCirclePolicy
open AspisR1CircleSampleWrapper
open R0P.SemSource

def nativePoint (p : QM31Exact × QM31Exact) : aspis_core.circle.SecureCirclePoint :=
  F3M_CircleSource.point (fromR72Point (encodePoint p))

def decodePublic (p : aspis_core.circle.SecureCirclePoint) : QM31Exact × QM31Exact :=
  (decode ⟨⟨p.x.c0.a,p.x.c0.b⟩,⟨p.x.c1.a,p.x.c1.b⟩⟩,
   decode ⟨⟨p.y.c0.a,p.y.c0.b⟩,⟨p.y.c1.a,p.y.c1.b⟩⟩)

theorem decoded (p : QM31Exact × QM31Exact) : decodePublic (nativePoint p)=p := by
  change decodePoint (encodePoint p)=p
  exact decode_point p

/-- The existing source execution law fixes the actual point without reducing inversion. -/
theorem source (block : Array U8 32#usize) (row : FinishModel.CircleRow)
    (q : AspisR1CircleSampleWrapper.field.QM31)
    (sample : _root_.sampler.qm31_sample block=ok q)
    (canon : Canonical (toR72QM q)) (outside : (decode (toR72QM q)).im ≠ 0) :
    F3M_CircleSource.source block row=ok (nativePoint (point (decode (toR72QM q)))) := by
  have hs := source_execution (toR72QM q) canon
  rw [outside_map _ outside] at hs
  have hm : _root_.circle.secure_ood_circle_point_from_parameter q=
      ok (.Ok (fromR72Point (encodePoint (point (decode (toR72QM q)))))) := by
    rw [AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw.secure_circle_eq_r72,hs]
    rfl
  exact F3M_CircleSourceCall.mapped block row _
    (AspisR1CircleSampleWrapper.RawCircleSampleEmittedWrapperLaw.success_returns_point
      block (F3M_CircleSource.row row) q _ sample hm)

theorem distinct (t u : QM31Exact) (ht : t.im ≠ 0) (hu : u.im ≠ 0) (different : t ≠ u) :
    nativePoint (point t) ≠ nativePoint (point u) := by
  intro same
  have decodedSame := congrArg decodePublic same
  rw [decoded,decoded] at decodedSame
  exact different (point_injective t u (outside_has_denominator t ht)
    (outside_has_denominator u hu) decodedSame)

theorem comparison (p q : aspis_core.circle.SecureCirclePoint) (different : p ≠ q) :
    FinishModel.pointEq p q=ok false := by
  rw [FinishModel.pointEq,FIr_FinishComparison.qm_eq_source,bind_tc_ok]
  by_cases hx : p.x=q.x
  · rw [if_pos (by simpa using hx),FIr_FinishComparison.qm_eq_source]
    have hy : p.y ≠ q.y := by
      intro h
      exact different (by cases p;cases q;cases hx;cases h;rfl)
    simp only [hy,decide_false]
  · simp only [hx,decide_false,Bool.false_eq_true,if_false]

#print axioms decoded
#print axioms source
#print axioms distinct
#print axioms comparison
end AspisR1.JFu_CircleAlgebra
end
