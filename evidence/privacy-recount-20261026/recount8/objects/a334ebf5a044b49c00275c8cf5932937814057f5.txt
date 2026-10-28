import R1Z.PV_RunJoin_WeightCarrier46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_WeightStateRoundtrip46
open Aeneas Aeneas.Std Result PV_RunJoin_WeightCarrier46
open PV_B2_F_ConstructorCarrier (amap)

def fromTag (v : U8) : PV_B2_251c1.transport.Variant :=
  if v=1#u8 then .S1 else if v=2#u8 then .S2 else .D

theorem tag_roundtrip (v : PV_B2_251c1.transport.Variant) : fromTag (tag v)=v := by
  cases v <;> rfl

theorem array_roundtrip {n : Usize} (a : Array Q n) :
    amap fromQ (amap toQ a)=a :=
  PV_B2_F_ConstructorCarrierLaws.amap_roundtrip _ _ q_roundtrip a

theorem matrix_roundtrip {n m : Usize} (a : Array (Array Q n) m) :
    amap (amap fromQ) (amap (amap toQ) a)=a :=
  PV_B2_F_ConstructorCarrierLaws.amap_roundtrip _ _ array_roundtrip a

theorem tensor_roundtrip {n m k : Usize} (a : Array (Array (Array Q n) m) k) :
    amap (amap (amap fromQ)) (amap (amap (amap toQ)) a)=a :=
  PV_B2_F_ConstructorCarrierLaws.amap_roundtrip _ _ matrix_roundtrip a

def fromState (s : State) : W :=
  ⟨fromTag s.1,amap (amap (amap fromQ)) s.2.1,
    amap (amap fromQ) s.2.2.1,amap fromQ s.2.2.2⟩

theorem complete (w : W) : fromState (state w)=w := by
  rcases w with ⟨v,f,p,e⟩
  simp only [fromState,state,tag_roundtrip,tensor_roundtrip,matrix_roundtrip,array_roundtrip]

#print axioms tag_roundtrip
#print axioms array_roundtrip
#print axioms matrix_roundtrip
#print axioms tensor_roundtrip
#print axioms complete
end R1Z.PV_RunJoin_WeightStateRoundtrip46
