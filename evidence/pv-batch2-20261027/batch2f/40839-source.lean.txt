import R1Z.PV_B2_C_ConstructorSuccess
import R1Z.PV_B2_F_MaterializeNative
set_option autoImplicit false
namespace PV_B2_F_ConstructorCarrier
open Aeneas Aeneas.Std Result
abbrev K := PV_B2_C_Carrier.aspis_core.field.QM31
abbrev Point := PV_B2_C_Carrier.aspis_core.circle.SecureCirclePoint
abbrev Variant := PV_B2_C_Carrier.transport.Variant
abbrev Weight := PV_B2_C_WeightsNative.host_weights.Weights
abbrev W := PV_B2_F_MaterializeNative.W
abbrev NQ := ProverRwFull.aspis_core.field.QM31
abbrev NP := ProverRwFull.aspis_core.circle.SecureCirclePoint
abbrev NV := ProverRwFull.transport.Variant

def amap {α β : Type} {n : Usize} (f : α → β) (a : Array α n) : Array β n :=
  ⟨a.val.map f,by rw [List.length_map,a.property]⟩

def fromQ (q : NQ) : K := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toQ (q : K) : NQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def to251Q (q : K) : PV_B2_251c1.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromPoint (p : NP) : Point := ⟨fromQ p.x,fromQ p.y⟩
def toPoint (p : Point) : NP := ⟨toQ p.x,toQ p.y⟩
def fromVariant : NV → Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D
def toVariant : Variant → NV
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D
def to251Variant : Variant → PV_B2_251c1.transport.Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

def toWeight (w : Weight) : W :=
  ⟨to251Variant w.variant,amap (amap (amap to251Q)) w.factors,
   amap (amap to251Q) w.points,amap to251Q w.extra⟩

def toError : PV_B2_C_Carrier.verifier.Error → ProverRwFull.verifier.Error
  | .Parse => .Parse
  | .Semantic => .Semantic
  | .Transcript => .Transcript
  | .Relation => .Relation
  | .Merkle => .Merkle
  | .Query => .Query
  | .Checkpoint => .Checkpoint
  | .Allocation => .Allocation
  | .Rejected => .Rejected
  | .AttemptsExhausted => .AttemptsExhausted
  | .Entropy => .Entropy

theorem q_roundtrip (q : NQ) : toQ (fromQ q)=q := by cases q; rfl
theorem q_roundtrip_kernel (q : K) : fromQ (toQ q)=q := by cases q; rfl
theorem point_roundtrip (p : NP) : toPoint (fromPoint p)=p := by cases p; rfl
theorem variant_roundtrip (v : NV) : toVariant (fromVariant v)=v := by cases v <;> rfl

theorem weight_factors (w : Weight) :
    (toWeight w).factors = amap (amap (amap to251Q)) w.factors := rfl
theorem weight_points (w : Weight) :
    (toWeight w).points = amap (amap to251Q) w.points := rfl
theorem weight_extra (w : Weight) : (toWeight w).extra = amap to251Q w.extra := rfl
#print axioms q_roundtrip
#print axioms q_roundtrip_kernel
#print axioms point_roundtrip
#print axioms variant_roundtrip
#print axioms weight_factors
#print axioms weight_points
#print axioms weight_extra
end PV_B2_F_ConstructorCarrier
