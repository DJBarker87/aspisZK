import RPu_FIz_ContributionList
import RPu_FIz_FamilyLengths
import R0P.SemDecision
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_ScalarAssembly
open FIv_NativeValue (K)
def part (xs : List K) (start i : Nat) : K :=
  if start ≤ i then (xs[i-start]?).getD 0 else 0

theorem outside (xs : List K) (start i : Nat) (hi : start+xs.length ≤ i) : part xs start i=0 := by
  unfold part
  rw [if_pos (by omega),List.getElem?_eq_none (by omega)]
  rfl

theorem inside (xs : List K) (start i : Nat) (hi : start ≤ i) : part xs start i=(xs[i-start]?).getD 0 := by
  exact if_pos hi

theorem value (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) (i : Nat) :
    part (R0P.scheduleFamily.residuals p o s) 0 i+
    part (R0P.pathFamily.residuals p o s) 32 i+
    part (R0P.valueFamily.residuals p o s) 49 i+
    part (R0P.digestFamily.residuals p o s) 84 i+
    part (R0P.assetFamily.residuals p o s) 92 i+
    part (R0P.occupancyFamily.residuals p o s) 0 i=
      R0P.SemSource.scalarLaneAt p o s i := by
  have ha : (R0P.assetFamily.residuals p o s).length=2 := by
    cases p.variant <;> cases p.withdrawalAmount <;> simp [R0P.assetFamily,R0P.assetScalarLanes]
  have ho : (R0P.occupancyFamily.residuals p o s).length=12 := by
    simp only [R0P.occupancyFamily,R0P.occupancyLanesLiteral,List.length_append,
      List.length_cons,List.length_nil,List.length_ofFn]
  unfold R0P.SemSource.scalarLaneAt
  simp only [List.getD]
  by_cases h12 : i<12
  · simp only [if_pos h12,part,Nat.zero_le,Nat.sub_zero,↓reduceIte]
    have h32 : ¬32 ≤ i := by omega
    have h49 : ¬49 ≤ i := by omega
    have h84 : ¬84 ≤ i := by omega
    have h92 : ¬92 ≤ i := by omega
    simp only [if_neg h32,if_neg h49,if_neg h84,if_neg h92,add_zero]
  · rw [if_neg h12,outside (R0P.occupancyFamily.residuals p o s) 0 i (by rw [ho];omega),add_zero]
    by_cases h32 : i<32
    · simp only [if_pos h32,part,Nat.zero_le,Nat.sub_zero,↓reduceIte,
        if_neg (show ¬32 ≤ i by omega),if_neg (show ¬49 ≤ i by omega),
        if_neg (show ¬84 ≤ i by omega),if_neg (show ¬92 ≤ i by omega),add_zero]
    · rw [if_neg h32,outside _ 0 i (by rw [FIz_FamilyLengths.schedule];omega),zero_add]
      by_cases h49 : i<49
      · simp only [if_pos h49,part,if_pos (show 32 ≤ i by omega),
          if_neg (show ¬49 ≤ i by omega),if_neg (show ¬84 ≤ i by omega),
          if_neg (show ¬92 ≤ i by omega),add_zero]
      · rw [if_neg h49,outside _ 32 i (by rw [FIz_FamilyLengths.path];omega),zero_add]
        by_cases h84 : i<84
        · simp only [if_pos h84,part,if_pos (show 49 ≤ i by omega),
            if_neg (show ¬84 ≤ i by omega),if_neg (show ¬92 ≤ i by omega),add_zero]
        · rw [if_neg h84,outside _ 49 i (by rw [FIz_FamilyLengths.value];omega),zero_add]
          by_cases h92 : i<92
          · simp only [if_pos h92,part,if_pos (show 84 ≤ i by omega),if_neg (show ¬92 ≤ i by omega),add_zero]
          · rw [if_neg h92,outside _ 84 i (by rw [FIz_FamilyLengths.digest];omega),zero_add]
            by_cases h94 : i<94
            · rw [if_pos h94,inside _ 92 i (by omega)]
            · rw [if_neg h94,outside _ 92 i (by rw [ha];omega)]
#print axioms outside
#print axioms inside
#print axioms value
end AspisR1.FIz_ScalarAssembly
end
