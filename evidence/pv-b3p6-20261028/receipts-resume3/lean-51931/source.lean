import PV_B3P_MaskModel132
namespace PV_B3P_MaskSource132
open PV_B3P_MaskModel132 PV_B3P_MaskShape132
set_option autoImplicit false

def legacyBase (level : Nat) : Nat := 864 + level/4*16 + 1 + 2*(level%4)
def legacyPath (r c : Nat) : Prop := ∃ level, level < 21 ∧
  ((r = legacyBase level ∧ c ≤ 8) ∨ r = legacyBase level+1 ∨
    (r = (legacyBase level ^^^ 12) ∧ c < 8))
def legacyValue (r c : Nat) : Prop :=
  (∃ value, value < 3 ∧ ((r = 960+2*value ∧ c ≤ 10) ∨
    (r = 960+2*value+1 ∧ c ≤ 10) ∨ (r = ((960+2*value) ^^^ 12) ∧ c ≤ 10))) ∨
  (r = 966 ∧ c < 3) ∨ (r = 967 ∧ c < 2)
def occupancy (r c : Nat) : Prop := (r = 969 ∧ c ≤ 10) ∨ (r = 970 ∧ c < 10)
def legacyUsed (r c : Nat) : Prop :=
  ¬(r < 864 ∨ 1024 ≤ r ∨ 16 ≤ c) ∧ (legacyPath r c ∨ legacyValue r c ∨ occupancy r c)

theorem legacy_bounds (level : Nat) (hl : level < 21) :
    legacyBase level+1 < 960 ∧ (legacyBase level ^^^ 12) < 960 := by
  constructor
  · unfold legacyBase
    omega
  · interval_cases level <;> decide

theorem legacy_path_absent (r c : Nat) (hr : 960 ≤ r) : ¬ legacyPath r c := by
  rintro ⟨level,hl,h⟩
  have hb := legacy_bounds level hl
  rcases h with ⟨h,_⟩ | h | ⟨h,_⟩ <;> omega

theorem exists_three (p : Nat → Prop) :
    (∃ v, v < 3 ∧ p v) ↔ p 0 ∨ p 1 ∨ p 2 := by
  constructor
  · rintro ⟨v,hv,h⟩
    have cases : v = 0 ∨ v = 1 ∨ v = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> tauto
  · rintro (h|h|h)
    · exact ⟨0,by omega,h⟩
    · exact ⟨1,by omega,h⟩
    · exact ⟨2,by omega,h⟩

theorem translated_value (r c : Nat) (lo : 1008 ≤ r) (hi : r < 1024) (hc : c < 16) :
    legacyUsed (r-48) c ↔ valueUsed (r-1008) c := by
  have hp := legacy_path_absent (r-48) c (by omega)
  simp only [legacyUsed,hp,false_or,legacyValue,exists_three,occupancy,valueUsed]
  norm_num only
  omega

-- The original forest predicate follows the same ordered path helper, then
-- translates the final sixteen rows into the legacy helper.
def nativeFree (r c : Nat) : Prop :=
  (r < 912 ∧ 13 ≤ r%16) ∨
    (¬r < 912 ∧ ¬(if r < 912 then False else if r < 1008 then pathUsed r c else legacyUsed (r-48) c))

theorem native_free (r c : Nat) (hr : r < 1024) (hc : c < 16) : nativeFree r c ↔ free r c := by
  by_cases h0 : r < 912
  · simp [nativeFree,free,h0]
  · by_cases h1 : r < 1008
    · simp only [nativeFree,free,h0,h1,↓reduceIte,false_and,false_or,true_and]
      exact (PV_B3P_MaskModel132.path r c (by omega) h1).symm
    · simp only [nativeFree,free,h0,h1,↓reduceIte,false_and,false_or,true_and]
      exact not_congr (translated_value r c (by omega) hr hc)

#print axioms legacy_bounds
#print axioms legacy_path_absent
#print axioms exists_three
#print axioms translated_value
#print axioms native_free
end PV_B3P_MaskSource132
