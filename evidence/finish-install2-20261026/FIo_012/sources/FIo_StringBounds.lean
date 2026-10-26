import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace AspisR1.FIo_StringBounds
theorem size_IndexOutOfRange : "IndexOutOfRange".toByteArray.size=15 := by
  change (String.ofList ['I','n','d','e','x','O','u','t','O','f','R','a','n','g','e']).toByteArray.size=15
  rw [String.toByteArray_ofList]
  rfl
theorem bound_IndexOutOfRange : "IndexOutOfRange".toByteArray.size≤U32.max := by
  rw [size_IndexOutOfRange]
  change 15≤4294967295
  omega
#print axioms size_IndexOutOfRange
#print axioms bound_IndexOutOfRange
theorem size_WrongLength : "WrongLength".toByteArray.size=11 := by
  change (String.ofList ['W','r','o','n','g','L','e','n','g','t','h']).toByteArray.size=11
  rw [String.toByteArray_ofList]
  rfl
theorem bound_WrongLength : "WrongLength".toByteArray.size≤U32.max := by
  rw [size_WrongLength]
  change 11≤4294967295
  omega
#print axioms size_WrongLength
#print axioms bound_WrongLength
theorem size_ZeroDenominator : "ZeroDenominator".toByteArray.size=15 := by
  change (String.ofList ['Z','e','r','o','D','e','n','o','m','i','n','a','t','o','r']).toByteArray.size=15
  rw [String.toByteArray_ofList]
  rfl
theorem bound_ZeroDenominator : "ZeroDenominator".toByteArray.size≤U32.max := by
  rw [size_ZeroDenominator]
  change 15≤4294967295
  omega
#print axioms size_ZeroDenominator
#print axioms bound_ZeroDenominator
theorem size_Allocation : "Allocation".toByteArray.size=10 := by
  change (String.ofList ['A','l','l','o','c','a','t','i','o','n']).toByteArray.size=10
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Allocation : "Allocation".toByteArray.size≤U32.max := by
  rw [size_Allocation]
  change 10≤4294967295
  omega
#print axioms size_Allocation
#print axioms bound_Allocation
theorem size_NonCanonical : "NonCanonical".toByteArray.size=12 := by
  change (String.ofList ['N','o','n','C','a','n','o','n','i','c','a','l']).toByteArray.size=12
  rw [String.toByteArray_ofList]
  rfl
theorem bound_NonCanonical : "NonCanonical".toByteArray.size≤U32.max := by
  rw [size_NonCanonical]
  change 12≤4294967295
  omega
#print axioms size_NonCanonical
#print axioms bound_NonCanonical
theorem size_WrongField : "WrongField".toByteArray.size=10 := by
  change (String.ofList ['W','r','o','n','g','F','i','e','l','d']).toByteArray.size=10
  rw [String.toByteArray_ofList]
  rfl
theorem bound_WrongField : "WrongField".toByteArray.size≤U32.max := by
  rw [size_WrongField]
  change 10≤4294967295
  omega
#print axioms size_WrongField
#print axioms bound_WrongField
theorem size_InvalidPoints : "InvalidPoints".toByteArray.size=13 := by
  change (String.ofList ['I','n','v','a','l','i','d','P','o','i','n','t','s']).toByteArray.size=13
  rw [String.toByteArray_ofList]
  rfl
theorem bound_InvalidPoints : "InvalidPoints".toByteArray.size≤U32.max := by
  rw [size_InvalidPoints]
  change 13≤4294967295
  omega
#print axioms size_InvalidPoints
#print axioms bound_InvalidPoints
theorem size_QuotientNotInImage : "QuotientNotInImage".toByteArray.size=18 := by
  change (String.ofList ['Q','u','o','t','i','e','n','t','N','o','t','I','n','I','m','a','g','e']).toByteArray.size=18
  rw [String.toByteArray_ofList]
  rfl
theorem bound_QuotientNotInImage : "QuotientNotInImage".toByteArray.size≤U32.max := by
  rw [size_QuotientNotInImage]
  change 18≤4294967295
  omega
#print axioms size_QuotientNotInImage
#print axioms bound_QuotientNotInImage
theorem size_RankDeficient : "RankDeficient".toByteArray.size=13 := by
  change (String.ofList ['R','a','n','k','D','e','f','i','c','i','e','n','t']).toByteArray.size=13
  rw [String.toByteArray_ofList]
  rfl
theorem bound_RankDeficient : "RankDeficient".toByteArray.size≤U32.max := by
  rw [size_RankDeficient]
  change 13≤4294967295
  omega
#print axioms size_RankDeficient
#print axioms bound_RankDeficient
theorem size_Parse : "Parse".toByteArray.size=5 := by
  change (String.ofList ['P','a','r','s','e']).toByteArray.size=5
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Parse : "Parse".toByteArray.size≤U32.max := by
  rw [size_Parse]
  change 5≤4294967295
  omega
#print axioms size_Parse
#print axioms bound_Parse
theorem size_Semantic : "Semantic".toByteArray.size=8 := by
  change (String.ofList ['S','e','m','a','n','t','i','c']).toByteArray.size=8
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Semantic : "Semantic".toByteArray.size≤U32.max := by
  rw [size_Semantic]
  change 8≤4294967295
  omega
#print axioms size_Semantic
#print axioms bound_Semantic
theorem size_Schedule : "Schedule".toByteArray.size=8 := by
  change (String.ofList ['S','c','h','e','d','u','l','e']).toByteArray.size=8
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Schedule : "Schedule".toByteArray.size≤U32.max := by
  rw [size_Schedule]
  change 8≤4294967295
  omega
#print axioms size_Schedule
#print axioms bound_Schedule
theorem size_Sampler : "Sampler".toByteArray.size=7 := by
  change (String.ofList ['S','a','m','p','l','e','r']).toByteArray.size=7
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Sampler : "Sampler".toByteArray.size≤U32.max := by
  rw [size_Sampler]
  change 7≤4294967295
  omega
#print axioms size_Sampler
#print axioms bound_Sampler
theorem size_Commitment : "Commitment".toByteArray.size=10 := by
  change (String.ofList ['C','o','m','m','i','t','m','e','n','t']).toByteArray.size=10
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Commitment : "Commitment".toByteArray.size≤U32.max := by
  rw [size_Commitment]
  change 10≤4294967295
  omega
#print axioms size_Commitment
#print axioms bound_Commitment
theorem size_Authentication : "Authentication".toByteArray.size=14 := by
  change (String.ofList ['A','u','t','h','e','n','t','i','c','a','t','i','o','n']).toByteArray.size=14
  rw [String.toByteArray_ofList]
  rfl
theorem bound_Authentication : "Authentication".toByteArray.size≤U32.max := by
  rw [size_Authentication]
  change 14≤4294967295
  omega
#print axioms size_Authentication
#print axioms bound_Authentication
theorem size_V1 : "V1".toByteArray.size=2 := by
  change (String.ofList ['V','1']).toByteArray.size=2
  rw [String.toByteArray_ofList]
  rfl
theorem bound_V1 : "V1".toByteArray.size≤U32.max := by
  rw [size_V1]
  change 2≤4294967295
  omega
#print axioms size_V1
#print axioms bound_V1
theorem size_V2 : "V2".toByteArray.size=2 := by
  change (String.ofList ['V','2']).toByteArray.size=2
  rw [String.toByteArray_ofList]
  rfl
theorem bound_V2 : "V2".toByteArray.size≤U32.max := by
  rw [size_V2]
  change 2≤4294967295
  omega
#print axioms size_V2
#print axioms bound_V2
end AspisR1.FIo_StringBounds
