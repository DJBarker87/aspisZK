import R1Z.PV_B2_F_RawNative
import R1Z.ProverCommitWeightsStorage53
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightCarrier46
open Aeneas Aeneas.Std Result
open PV_B2_F_ConstructorCarrier (amap)
abbrev Q := PV_B2_251c1.aspis_core.field.QM31
abbrev W := PV_B2_F_MaterializeNative.W
abbrev MQ := AspisR1ProducerRelease47.field.QM31
abbrev State := ProverCommitWeightsStorage53.State

def toQ (q : Q) : MQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromQ (q : MQ) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def tag : PV_B2_251c1.transport.Variant → U8
  | .S1 => 1#u8
  | .S2 => 2#u8
  | .D => 0#u8
def state (w : W) : State :=
  (tag w.variant,amap (amap (amap toQ)) w.factors,
   amap (amap toQ) w.points,amap toQ w.extra)

theorem q_roundtrip (q : Q) : fromQ (toQ q)=q := by cases q; rfl
theorem model_roundtrip (q : MQ) : toQ (fromQ q)=q := by cases q; rfl
theorem variant (w : W) : (state w).1=tag w.variant := rfl
theorem factors (w : W) : (state w).2.1=amap (amap (amap toQ)) w.factors := rfl
theorem points (w : W) : (state w).2.2.1=amap (amap toQ) w.points := rfl
theorem extra (w : W) : (state w).2.2.2=amap toQ w.extra := rfl

#print axioms q_roundtrip
#print axioms model_roundtrip
#print axioms variant
#print axioms factors
#print axioms points
#print axioms extra
end R1Z.PV_RunJoin_WeightCarrier46
