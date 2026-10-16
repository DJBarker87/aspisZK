import ValueLaneResidualList
import ValueLanePackedComposition

/-! Symbolic assembly of the six source family intervals, including the
schedule/occupancy overlap and the two final zero padding slots. -/
set_option autoImplicit false
namespace AspisR1.SemanticPackedIntervalAssembly
open AspisR1.ValueLaneResidualList

variable {K : Type} [Field K]

theorem selectList_getD (start index : Nat) (xs : List K) (hstart : start ≤ index) :
    selectList start xs index = xs.getD (index-start) 0 := by
  by_cases hi : index-start < xs.length
  · rw [selectList, dif_pos (by omega), List.getD_eq_getElem _ _ hi]
  · rw [selectList, dif_neg (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), Option.getD_none]

theorem selectList_before (start index : Nat) (xs : List K) (hi : index < start) :
    selectList start xs index = 0 := by
  rw [selectList, dif_neg (by omega)]

theorem selectList_after (start index : Nat) (xs : List K) (hi : start+xs.length ≤ index) :
    selectList start xs index = 0 := by
  rw [selectList, dif_neg (by omega)]

def slot (schedule path value occupancy digest asset : List K) (index : Nat) : K :=
  if index < 12 then schedule.getD index 0 + occupancy.getD index 0
  else if index < 32 then schedule.getD index 0
  else if index < 49 then path.getD (index-32) 0
  else if index < 84 then value.getD (index-49) 0
  else if index < 92 then digest.getD (index-84) 0
  else if index < 94 then asset.getD (index-92) 0
  else 0

theorem intervals_eq_slot (schedule path value occupancy digest asset : List K)
    (hs : schedule.length = 32) (hp : path.length = 17) (hv : value.length = 35)
    (ho : occupancy.length = 12) (hd : digest.length = 8) (ha : asset.length = 2)
    (index : Nat) :
    (((((selectList 0 schedule index + selectList 32 path index) + selectList 49 value index) +
      selectList 0 occupancy index) + selectList 84 digest index) + selectList 92 asset index) =
      slot schedule path value occupancy digest asset index := by
  by_cases h12 : index < 12
  · simp only [slot, if_pos h12, selectList_getD 0 index schedule (by omega),
      selectList_before 32 index path (by omega), selectList_before 49 index value (by omega),
      selectList_getD 0 index occupancy (by omega), selectList_before 84 index digest (by omega),
      selectList_before 92 index asset (by omega), Nat.sub_zero, add_zero]
  · by_cases h32 : index < 32
    · simp only [slot, if_neg h12, if_pos h32, selectList_getD 0 index schedule (by omega),
        selectList_before 32 index path (by omega), selectList_before 49 index value (by omega),
        selectList_after 0 index occupancy (by omega), selectList_before 84 index digest (by omega),
        selectList_before 92 index asset (by omega), Nat.sub_zero, add_zero]
    · by_cases h49 : index < 49
      · simp only [slot, if_neg h12, if_neg h32, if_pos h49,
          selectList_after 0 index schedule (by omega), selectList_getD 32 index path (by omega),
          selectList_before 49 index value (by omega), selectList_after 0 index occupancy (by omega),
          selectList_before 84 index digest (by omega), selectList_before 92 index asset (by omega),
          add_zero, zero_add]
      · by_cases h84 : index < 84
        · simp only [slot, if_neg h12, if_neg h32, if_neg h49, if_pos h84,
            selectList_after 0 index schedule (by omega), selectList_after 32 index path (by omega),
            selectList_getD 49 index value (by omega), selectList_after 0 index occupancy (by omega),
            selectList_before 84 index digest (by omega), selectList_before 92 index asset (by omega),
            add_zero, zero_add]
        · by_cases h92 : index < 92
          · simp only [slot, if_neg h12, if_neg h32, if_neg h49, if_neg h84, if_pos h92,
              selectList_after 0 index schedule (by omega), selectList_after 32 index path (by omega),
              selectList_after 49 index value (by omega), selectList_after 0 index occupancy (by omega),
              selectList_getD 84 index digest (by omega), selectList_before 92 index asset (by omega),
              add_zero, zero_add]
          · by_cases h94 : index < 94
            · simp only [slot, if_neg h12, if_neg h32, if_neg h49, if_neg h84, if_neg h92, if_pos h94,
                selectList_after 0 index schedule (by omega), selectList_after 32 index path (by omega),
                selectList_after 49 index value (by omega), selectList_after 0 index occupancy (by omega),
                selectList_after 84 index digest (by omega), selectList_getD 92 index asset (by omega),
                add_zero, zero_add]
            · simp only [slot, if_neg h12, if_neg h32, if_neg h49, if_neg h84, if_neg h92, if_neg h94,
                selectList_after 0 index schedule (by omega), selectList_after 32 index path (by omega),
                selectList_after 49 index value (by omega), selectList_after 0 index occupancy (by omega),
                selectList_after 84 index digest (by omega), selectList_after 92 index asset (by omega),
                add_zero]

theorem pack_intervals {F : Subfield K} (B : R0P.PackBasis F)
    (schedule path value occupancy digest asset : List K)
    (hs : schedule.length = 32) (hp : path.length = 17) (hv : value.length = 35)
    (ho : occupancy.length = 12) (hd : digest.length = 8) (ha : asset.length = 2)
    (group : Nat) :
    (((((R0P.pack4 B (fun k => selectList 0 schedule (4*group+k.val)) +
      R0P.pack4 B (fun k => selectList 32 path (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 49 value (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 0 occupancy (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 84 digest (4*group+k.val))) +
      R0P.pack4 B (fun k => selectList 92 asset (4*group+k.val))) =
    R0P.pack4 B (fun k => slot schedule path value occupancy digest asset (4*group+k.val)) := by
  simp only [← AspisR1.ValueLanePackedComposition.pack_add]
  congr 1
  funext k
  exact intervals_eq_slot schedule path value occupancy digest asset hs hp hv ho hd ha _

#print axioms selectList_getD
#print axioms intervals_eq_slot
#print axioms pack_intervals
end AspisR1.SemanticPackedIntervalAssembly
