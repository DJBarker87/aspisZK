import R1Z.PV_B2_F_ConstructorCarrier
set_option autoImplicit false
namespace PV_B2_F_ConstructorCarrierLaws
open Aeneas Aeneas.Std Result PV_B2_F_ConstructorCarrier

theorem amap_roundtrip {α β : Type} {n : Usize} (f : α → β) (g : β → α)
    (h : ∀ x,g (f x)=x) (a : Array α n) : amap g (amap f a)=a := by
  apply Subtype.ext
  change (a.val.map f).map g = a.val
  simp [List.map_map,Function.comp_def,h]

def from251Q (q : PV_B2_251c1.aspis_core.field.QM31) : K :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def from251Variant : PV_B2_251c1.transport.Variant → Variant
  | .S1 => .S1
  | .S2 => .S2
  | .D => .D

theorem q_roundtrip (q : K) : from251Q (to251Q q)=q := by cases q; rfl
theorem variant_roundtrip (v : Variant) : from251Variant (to251Variant v)=v := by cases v <;> rfl

theorem q_array_roundtrip {n : Usize} (a : Array K n) :
    amap from251Q (amap to251Q a)=a := amap_roundtrip _ _ q_roundtrip a

theorem q_matrix_roundtrip {n m : Usize} (a : Array (Array K n) m) :
    amap (amap from251Q) (amap (amap to251Q) a)=a :=
  amap_roundtrip _ _ q_array_roundtrip a

theorem q_tensor_roundtrip {n m k : Usize} (a : Array (Array (Array K n) m) k) :
    amap (amap (amap from251Q)) (amap (amap (amap to251Q)) a)=a :=
  amap_roundtrip _ _ q_matrix_roundtrip a

def fromWeight (w : W) : Weight :=
  ⟨from251Variant w.variant,amap (amap (amap from251Q)) w.factors,
   amap (amap from251Q) w.points,amap from251Q w.extra⟩

theorem weight_roundtrip (w : Weight) : fromWeight (toWeight w)=w := by
  rcases w with ⟨v,f,p,e⟩
  simp only [fromWeight,toWeight,variant_roundtrip,q_tensor_roundtrip,q_matrix_roundtrip,q_array_roundtrip]

theorem alpha_roundtrip (alpha : Array NQ 10#usize) : amap toQ (amap fromQ alpha)=alpha :=
  amap_roundtrip _ _ PV_B2_F_ConstructorCarrier.q_roundtrip alpha

theorem points_roundtrip (z : Array NP 2#usize) : amap toPoint (amap fromPoint z)=z :=
  amap_roundtrip _ _ PV_B2_F_ConstructorCarrier.point_roundtrip z
#print axioms amap_roundtrip
#print axioms q_roundtrip
#print axioms variant_roundtrip
#print axioms q_array_roundtrip
#print axioms q_matrix_roundtrip
#print axioms q_tensor_roundtrip
#print axioms weight_roundtrip
#print axioms alpha_roundtrip
#print axioms points_roundtrip
end PV_B2_F_ConstructorCarrierLaws
