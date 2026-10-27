import RPu_FJk_OccupancyMap
import RPu_FJk_ListMap
import RPu_ScheduleFamilyFieldTransport
import RPu_PathFamilyFieldTransport
import RPu_ValueFamilyFieldTransport
import RPu_DigestFamilyFieldTransport
import RPu_AssetFamilyFieldTransport
import R0P.SemDecision
set_option autoImplicit false
namespace AspisR1.FJk_ScalarLaneMap
variable {K L : Type} [Field K] [Field L]
/-- All six families and their zero defaults commute with the SAME field map. -/
theorem value (f : K →+* L) (pub : R0P.Public K) (o : R0P.Openings K)
    (sel : R0P.Sel K) (index : Nat) :
    f (R0P.SemSource.scalarLaneAt pub o sel index)=
    R0P.SemSource.scalarLaneAt (SpendDataMap.mapPublic f pub)
      (ValueFamilyFieldTransport.mapOpenings f o) (fun i=>f (sel i)) index := by
  let pw := SpendDataMap.mapPublic f pub
  have hsch := ScheduleFamilyFieldTransport.map_family f pub pw o sel rfl
  have hocc := FJk_OccupancyMap.value f pub o sel
  have hpath := PathFamilyFieldTransport.map_family f pub pw o sel
  have hvalue := ValueFamilyFieldTransport.map_family f pub pw o sel
  have hdigest := DigestFamilyFieldTransport.map_family f pub o sel
  have hasset := AssetFamilyFieldTransport.map_family f pub pw o sel rfl rfl rfl
  unfold R0P.SemSource.scalarLaneAt
  by_cases h12 : index<12
  · simp only [if_pos h12,map_add]
    rw [FJk_ListMap.getD,hsch,FJk_ListMap.getD,hocc]
  · simp only [if_neg h12]
    by_cases h32 : index<32
    · simp only [if_pos h32]
      rw [FJk_ListMap.getD,hsch]
    · simp only [if_neg h32]
      by_cases h49 : index<49
      · simp only [if_pos h49]
        rw [FJk_ListMap.getD,hpath]
      · simp only [if_neg h49]
        by_cases h84 : index<84
        · simp only [if_pos h84]
          rw [FJk_ListMap.getD,hvalue]
        · simp only [if_neg h84]
          by_cases h92 : index<92
          · simp only [if_pos h92]
            rw [FJk_ListMap.getD,hdigest]
          · simp only [if_neg h92]
            by_cases h94 : index<94
            · simp only [if_pos h94]
              rw [FJk_ListMap.getD,hasset]
            · simp only [if_neg h94,map_zero]
#print axioms value
end AspisR1.FJk_ScalarLaneMap
