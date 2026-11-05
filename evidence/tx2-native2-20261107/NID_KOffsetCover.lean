import NHV_COMBINED_IMPORT
set_option autoImplicit false
namespace NID_KOffsetCover

def Allowed (offset : Nat) : Prop := offset=304 ∨ ∃ row, row<83 ∧ offset=408+16*row

theorem rho : Allowed 304 := Or.inl rfl

theorem semantic (i : Nat) (live : i<10) : Allowed (408+16*i) :=
 Or.inr ⟨i,by omega,rfl⟩

theorem coordinates : Allowed 568 ∧ Allowed 584 ∧ Allowed 600 ∧ Allowed 616 := by
 exact ⟨Or.inr ⟨10,by decide,rfl⟩,Or.inr ⟨11,by decide,rfl⟩,
  Or.inr ⟨12,by decide,rfl⟩,Or.inr ⟨13,by decide,rfl⟩⟩

theorem power : Allowed 696 := Or.inr ⟨18,by decide,rfl⟩

theorem weights (i : Nat) (live : i<64) : Allowed (712+16*i) := by
 right
 refine ⟨19+i,by omega,?_⟩
 omega

theorem bounded (offset : Nat) (allowed : Allowed offset) : offset+16≤1768 := by
 rcases allowed with rfl | ⟨row,live,rfl⟩ <;> omega
#print axioms rho
#print axioms semantic
#print axioms coordinates
#print axioms power
#print axioms weights
#print axioms bounded
end NID_KOffsetCover
