import R1Z.PV_OWN_View
set_option autoImplicit false
namespace R1Z.PV_OWNI_EntryBytes
open PV_OWN_Bytes PV_OWN_View
/-- Deployed 64-bit usize plus four u32 limbs, viewed as their little-endian
bytes. All 24 bytes are active; numeric field interpretation is separate. -/
abbrev Entry := (Fin 8 → UInt8) × (Fin 16 → UInt8)
def encode (v : Entry) : Bytes := fun i =>
 if h:i<8 then some (v.1 ⟨i,h⟩) else
 if h:i<24 then some (v.2 ⟨i-8,by omega⟩) else none

theorem row (v : Entry) (i : Fin 8) : encode v i=some (v.1 i) := by
 simp only [encode,i.isLt,dif_pos]
theorem limbs (v : Entry) (i : Fin 16) : encode v (8+i.val)=some (v.2 i) := by
 simp only [encode,show ¬8+i.val<8 by omega,dif_neg,
   show 8+i.val<24 by omega,dif_pos,Nat.add_sub_cancel_left, dite_false]
theorem bounded (v : Entry) (i : Nat) (b : UInt8) (h:encode v i=some b) : i<24 := by
 by_cases hn:i<24
 · exact hn
 · have h8:¬i<8 := by omega
   simp only [encode,h8,dite_false,hn] at h
   cases h
theorem injective (a b : Entry) (h:∀ i,i<24 → encode a i=encode b i) : a=b := by
 apply Prod.ext
 · funext i
   exact Option.some.inj ((row a i).symm.trans ((h i (by omega)).trans (row b i)))
 · funext i
   exact Option.some.inj ((limbs a i).symm.trans ((h (8+i.val) (by omega)).trans (limbs b i)))
def codec : Codec Entry := ⟨24,8,by decide,encode,injective⟩
#print axioms row
#print axioms limbs
#print axioms bounded
#print axioms injective
end R1Z.PV_OWNI_EntryBytes
