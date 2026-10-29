import R1Z.PV_RunJoin_ClaimEvaluation49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimEvaluationActual50
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46
open PV_B2_F_ConstructorCarrier (amap)
open ProverRwDictionaryTower (toW fromW)
open PV_RunJoin_ClaimThread48 (Point Column W)

def run (p : Point) (q : Column) : Result W :=
  PV_RunJoin_WeightMap46.mapResult fromW
    (PV_RunJoin_EncoderValue49.run (amap toW q) (toW p.x) (toW p.y))

theorem array_roundtrip (q : Column) : amap fromW (amap toW q)=q := by
  apply Subtype.ext
  simp only [amap,List.map_map,Function.comp_def,ProverRwDictionaryTower.w_roundtrip]
  exact List.map_id _

theorem point_roundtrip (p : Point) :
    (⟨fromW (toW p.x),fromW (toW p.y)⟩ : Point)=p := by
  cases p
  simp only [ProverRwDictionaryTower.w_roundtrip]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    (p : Point) (q : Column) :
    PV_RunJoin_ClaimProducerCell48.evaluate base heap box (@PV_DL_EncoderSelected.selected (types base) ops) p q=
      run p q := by
  have h := PV_RunJoin_ClaimEvaluation49.complete base heap box ops (amap toW q) (toW p.x) (toW p.y)
  rw [array_roundtrip,point_roundtrip] at h
  exact h
#print axioms run
#print axioms array_roundtrip
#print axioms point_roundtrip
#print axioms complete
end R1Z.PV_RunJoin_ClaimEvaluationActual50
