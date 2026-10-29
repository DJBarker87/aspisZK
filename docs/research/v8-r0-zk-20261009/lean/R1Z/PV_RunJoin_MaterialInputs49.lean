import R1Z.PV_RunJoin_OpeningConstructor48
import R1Z.ProverCommitWeightsMaterial53
set_option autoImplicit false
namespace R1Z.PV_RunJoin_MaterialInputs49
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open PV_B2_F_ConstructorCarrier (amap)
abbrev MQ := AspisR1ProducerRelease47.field.QM31

def alpha (p : Nat → Old.Q) : Array aspis_core.field.QM31 10#usize :=
  amap ProverRwDictionaryTower.fromQ (ProverCommitQArray48.array 10#usize p)
def point (x y : Old.Q) : aspis_core.circle.SecureCirclePoint :=
  ⟨ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source x),
   ProverRwDictionaryTower.fromQ (ProverCommitNativeQ48.source y)⟩
def points (x0 y0 x1 y1 : Old.Q) : Array aspis_core.circle.SecureCirclePoint 2#usize :=
  Array.make 2#usize [point x0 y0,point x1 y1]

theorem scalar (q : MQ) :
    PV_RunJoin_WeightKernel46.toQ (PV_B2_F_ConstructorCarrier.fromQ (ProverRwDictionaryTower.fromQ q))=q := by
  cases q;rfl

theorem alpha_model (p : Nat → Old.Q) :
    amap PV_RunJoin_WeightKernel46.toQ (amap PV_B2_F_ConstructorCarrier.fromQ (alpha p))=
      ProverCommitQArray48.array 10#usize p := by
  apply Subtype.ext
  simp only [alpha,amap,List.map_map,Function.comp_def]
  have identity : (fun q : MQ => PV_RunJoin_WeightKernel46.toQ
      (PV_B2_F_ConstructorCarrier.fromQ (ProverRwDictionaryTower.fromQ q)))=id := by
    funext q
    exact scalar q
  rw [identity,List.map_id]

theorem read0 (x0 y0 x1 y1 : Old.Q) :
    Array.index_usize (amap PV_B2_F_ConstructorCarrier.fromPoint (points x0 y0 x1 y1)) 0#usize=
      ok (PV_B2_F_ConstructorCarrier.fromPoint (point x0 y0)) := rfl

theorem read1 (x0 y0 x1 y1 : Old.Q) :
    Array.index_usize (amap PV_B2_F_ConstructorCarrier.fromPoint (points x0 y0 x1 y1)) 1#usize=
      ok (PV_B2_F_ConstructorCarrier.fromPoint (point x1 y1)) := rfl

theorem x_model (x y : Old.Q) :
    PV_RunJoin_WeightKernel46.toQ (PV_B2_F_ConstructorCarrier.fromPoint (point x y)).x=
      ProverCommitNativeQ48.source x := scalar _
theorem y_model (x y : Old.Q) :
    PV_RunJoin_WeightKernel46.toQ (PV_B2_F_ConstructorCarrier.fromPoint (point x y)).y=
      ProverCommitNativeQ48.source y := scalar _
#print axioms alpha
#print axioms point
#print axioms points
#print axioms scalar
#print axioms alpha_model
#print axioms read0
#print axioms read1
#print axioms x_model
#print axioms y_model
end R1Z.PV_RunJoin_MaterialInputs49
