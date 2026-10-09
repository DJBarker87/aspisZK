import SelectedCopyLayoutRows

/-! The literal selected 136-link layout has separate injective producer and
consumer placements. This converts the already-constructed weighted row
balance into the actual active-link rational balance. The slot values are
never multiplied by, or deleted according to, public weights.

The sum argument is a weighted port of NativePaymentCompiledCopyLogUpV1's
slot-to-link proof; no old native registry or uncached closure is imported.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000
set_option maxHeartbeats 150000

namespace AspisV8.SelectedCopyLinkBalance
open scoped BigOperators
open AspisV8.SelectedWeightedCopyCore
open AspisV8.SelectedWeightedCopyRows
open AspisV8.SelectedCopyLayout
open AspisV8.SelectedCopyLayoutRows

def placement (endpoint : Endpoint) : Fin 1024 × Fin 2 :=
  (endpoint.row, endpoint.slot)

/-- Explicit public lookup keys avoid reducing an all-pairs injectivity
problem. The left-inverse certificates below check each literal source
endpoint once against the lookup; no independently trusted layout is added. -/
def producerKeys : List Nat := [
  54,86,822,886,918,982,1014,22,
  24,88,120,89,920,1016,2016,2020,
  2024,2028,128,1826,1046,950,1047,2036,
  1078,1079,1110,1111,1142,1143,1174,1175,
  1206,1207,1238,1239,1270,1271,1302,1303,
  1334,1335,1366,1367,1398,1399,1430,1431,
  1462,1463,1494,1495,1526,1527,1558,1559,
  1590,1591,1622,1623,1654,1655,1686,1687,
  118,1828,1829,150,1836,1837,182,1844,
  1845,214,1852,1853,246,1860,1861,278,
  1868,1869,310,1876,1877,342,1884,1885,
  374,1892,1893,406,1900,1901,438,1908,
  1909,470,1916,1917,502,1924,1925,534,
  1932,1933,566,1940,1941,598,1948,1949,
  630,1956,1957,662,1964,1965,694,1972,
  1973,726,1980,1981,758,1988,1989,790,
  1996,1997,1750,2004,2005,1782,2012,2013]

def consumerKeys : List Nat := [
  64,96,832,896,928,992,1024,56,
  824,856,857,2016,2020,2024,2028,2029,
  2030,2031,2034,2035,2036,1080,1081,1056,
  1112,1088,1144,1120,1176,1152,1208,1184,
  1240,1216,1272,1248,1304,1280,1336,1312,
  1368,1344,1400,1376,1432,1408,1464,1440,
  1496,1472,1528,1504,1560,1536,1592,1568,
  1624,1600,1656,1632,1688,1664,1720,1696,
  1826,152,128,1834,184,160,1842,216,
  192,1850,248,224,1858,280,256,1866,
  312,288,1874,344,320,1882,376,352,
  1890,408,384,1898,440,416,1906,472,
  448,1914,504,480,1922,536,512,1930,
  568,544,1938,600,576,1946,632,608,
  1954,664,640,1962,696,672,1970,728,
  704,1978,760,736,1986,792,768,1994,
  1752,1728,2002,1784,1760,2010,1816,1792]

def endpointKey (endpoint : Endpoint) : Nat :=
  2 * endpoint.row.val + endpoint.slot.val

theorem producer_key_left_inverse : ∀ index : Fin 136,
    producerKeys.idxOf (endpointKey (sourceLinks index).producer) = index.val := by
  decide

theorem consumer_key_left_inverse : ∀ index : Fin 136,
    consumerKeys.idxOf (endpointKey (sourceLinks index).consumer) = index.val := by
  decide

/-- Separate sides may share a row/slot; within either side each slot has
at most one link, derived symbolically from the linear-size certificates. -/
theorem producer_placement_injective :
    Function.Injective (fun index => placement (sourceLinks index).producer) := by
  intro left right same
  apply Fin.ext
  calc
    left.val = producerKeys.idxOf (endpointKey (sourceLinks left).producer) :=
      (producer_key_left_inverse left).symm
    _ = producerKeys.idxOf (endpointKey (sourceLinks right).producer) :=
      congrArg (fun target : Fin 1024 × Fin 2 =>
        producerKeys.idxOf (2 * target.1.val + target.2.val)) same
    _ = right.val := producer_key_left_inverse right

theorem consumer_placement_injective :
    Function.Injective (fun index => placement (sourceLinks index).consumer) := by
  intro left right same
  apply Fin.ext
  calc
    left.val = consumerKeys.idxOf (endpointKey (sourceLinks left).consumer) :=
      (consumer_key_left_inverse left).symm
    _ = consumerKeys.idxOf (endpointKey (sourceLinks right).consumer) :=
      congrArg (fun target : Fin 1024 × Fin 2 =>
        consumerKeys.idxOf (2 * target.1.val + target.2.val)) same
    _ = right.val := consumer_key_left_inverse right

variable {K : Type*} [Field K]

theorem gather_at_placement (endpoint : Fin 136 → Endpoint)
    (unique : Function.Injective (fun index => placement (endpoint index)))
    (value : Fin 136 → K) (index : Fin 136) :
    gather endpoint value (endpoint index).row (endpoint index).slot = value index := by
  classical
  unfold gather
  rw [Finset.sum_eq_single index]
  · simp [slotContribution]
  · intro other _ different
    apply if_neg
    intro same
    exact different (unique (Prod.ext same.1 same.2))
  · simp

theorem gather_unoccupied (endpoint : Fin 136 → Endpoint)
    (value : Fin 136 → K) (row : Fin 1024) (slot : Fin 2)
    (empty : ¬∃ index, (endpoint index).row = row ∧ (endpoint index).slot = slot) :
    gather endpoint value row slot = 0 := by
  unfold gather
  apply Finset.sum_eq_zero
  intro index _
  apply if_neg
  intro occupied
  exact empty ⟨index, occupied⟩

/-- This identity does not require any denominator premise: field inverse
is total. Non-poles remain necessary in the separate residual-to-helper step. -/
theorem weighted_slot_eq_gather (endpoint : Fin 136 → Endpoint)
    (unique : Function.Injective (fun index => placement (endpoint index)))
    (value weight : Fin 136 → K) (chi : K) (row : Fin 1024) (slot : Fin 2) :
    gather endpoint weight row slot * (chi - gather endpoint value row slot)⁻¹ =
      gather endpoint (fun index => weight index * (chi - value index)⁻¹) row slot := by
  classical
  by_cases occupied : ∃ index, (endpoint index).row = row ∧ (endpoint index).slot = slot
  · obtain ⟨index, rowEqual, slotEqual⟩ := occupied
    subst row
    subst slot
    rw [gather_at_placement endpoint unique weight,
      gather_at_placement endpoint unique value,
      gather_at_placement endpoint unique]
  · rw [gather_unoccupied endpoint weight row slot occupied, zero_mul]
    exact (gather_unoccupied endpoint _ row slot occupied).symm

theorem sum_gather (endpoint : Fin 136 → Endpoint) (value : Fin 136 → K) :
    (∑ row : Fin 1024, ∑ slot : Fin 2, gather endpoint value row slot) =
      ∑ index : Fin 136, value index := by
  classical
  unfold gather
  calc
    _ = ∑ row : Fin 1024, ∑ index : Fin 136, ∑ slot : Fin 2,
        slotContribution (endpoint index) row slot (value index) := by
      apply Finset.sum_congr rfl
      intro row _
      exact Finset.sum_comm
    _ = ∑ index : Fin 136, ∑ row : Fin 1024, ∑ slot : Fin 2,
        slotContribution (endpoint index) row slot (value index) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      simp [slotContribution, ite_and, eq_comm]

theorem sum_weighted_slots (endpoint : Fin 136 → Endpoint)
    (unique : Function.Injective (fun index => placement (endpoint index)))
    (value weight : Fin 136 → K) (chi : K) :
    (∑ row : Fin 1024, ∑ slot : Fin 2,
      gather endpoint weight row slot * (chi - gather endpoint value row slot)⁻¹) =
      ∑ index : Fin 136, weight index * (chi - value index)⁻¹ := by
  simp_rw [weighted_slot_eq_gather endpoint unique value weight chi]
  exact sum_gather endpoint _

def linkBalance (table : Table K) (lambda chi : K)
    (variant : Variant) (appendIndex : Nat) : K :=
  ∑ index : Fin 136, selectedWeight variant appendIndex index *
    ((chi - compressed table lambda index (sourceLinks index).producer)⁻¹ -
      (chi - compressed table lambda index (sourceLinks index).consumer)⁻¹)

/-- Exact sum over the selected public active-link set, not over an old
transfer-only/native registry. No inactive tuple equality is asserted. -/
def activeLinkBalance (table : Table K) (lambda chi : K)
    (variant : Variant) (appendIndex : Nat) : K :=
  ∑ index : Fin 136,
    if weightBit variant appendIndex (selectedKind index) then
      (chi - compressed table lambda index (sourceLinks index).producer)⁻¹ -
        (chi - compressed table lambda index (sourceLinks index).consumer)⁻¹
    else 0

theorem linkBalance_eq_active (table : Table K) (lambda chi : K)
    (variant : Variant) (appendIndex : Nat) :
    linkBalance table lambda chi variant appendIndex =
      activeLinkBalance table lambda chi variant appendIndex := by
  unfold linkBalance activeLinkBalance
  apply Finset.sum_congr rfl
  intro index _
  unfold selectedWeight publicWeight
  split <;> simp_all

/-- The substantive new bridge: the whole constructed Boolean row sum is
the weighted link sum with actual endpoints/patterns and their own tags. -/
theorem source_rows_eq_link_balance (table : Table K) (lambda chi : K)
    (variant : Variant) (appendIndex : Nat) :
    (∑ row, rationalContribution (sourceRows table lambda variant appendIndex row) chi) =
      linkBalance table lambda chi variant appendIndex := by
  simp only [rationalContribution, sourceRows]
  rw [Finset.sum_sub_distrib,
    sum_weighted_slots _ producer_placement_injective,
    sum_weighted_slots _ consumer_placement_injective,
    ← Finset.sum_sub_distrib]
  unfold linkBalance
  apply Finset.sum_congr rfl
  intro index _
  exact (mul_sub _ _ _).symm

theorem source_active_links_zero (table : Table K) (lambda chi : K)
    (variant : Variant) (appendIndex : Nat) (helper : Fin 1024 → K)
    (localZero : ∀ row,
      selectedBooleanResidual (sourceRows table lambda variant appendIndex)
        helper chi row = 0)
    (totalZero : (∑ row, helper row) = 0)
    (inactiveZero : (∑ row, inactiveHelper rowActive helper row) = 0)
    (noPole : ∀ row, rowActive row →
      NoSlotPole (sourceRows table lambda variant appendIndex row) chi) :
    activeLinkBalance table lambda chi variant appendIndex = 0 := by
  rw [← linkBalance_eq_active, ← source_rows_eq_link_balance]
  exact source_layout_balance_zero table lambda variant appendIndex helper chi
    localZero totalZero inactiveZero noPole

#print axioms producer_key_left_inverse
#print axioms consumer_key_left_inverse
#print axioms producer_placement_injective
#print axioms consumer_placement_injective
#print axioms gather_at_placement
#print axioms gather_unoccupied
#print axioms weighted_slot_eq_gather
#print axioms sum_gather
#print axioms sum_weighted_slots
#print axioms linkBalance_eq_active
#print axioms source_rows_eq_link_balance
#print axioms source_active_links_zero
end AspisV8.SelectedCopyLinkBalance
