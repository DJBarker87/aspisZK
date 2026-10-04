import AspisV8R17.IndexSchedule
/-! The finite index-only schedules used by the R748 transpose entry. -/
set_option autoImplicit false
namespace AspisV8R19.R748FiniteGatherSchedules
open AspisV8R17

lemma loop191 : indexLoop 10 191 0 = some
    [(190,1),(188,2),(184,3),(176,4),(160,5),(128,6),(192,6)] := by rfl
lemma loop188 : indexLoop 10 188 0 = some [(189,0)] := by rfl
lemma loop3 : indexLoop 10 3 0 = some [(2,1),(0,2),(4,2)] := by rfl
lemma loop0 : indexLoop 10 0 0 = some [(1,0)] := by rfl

lemma loop94 : indexLoop 10 94 0 = some [(95,0)] := by rfl
lemma loop95 : indexLoop 10 95 0 = some
    [(94,1),(92,2),(88,3),(80,4),(64,5),(96,5)] := by rfl
lemma loop1 : indexLoop 10 1 0 = some [(0,1),(2,1)] := by rfl
lemma loop2 : indexLoop 10 2 0 = some [(3,0)] := by rfl
lemma loop64 : indexLoop 10 64 0 = some [(65,0)] := by rfl
lemma loop80 : indexLoop 10 80 0 = some [(81,0)] := by rfl
lemma loop88 : indexLoop 10 88 0 = some [(89,0)] := by rfl
lemma loop92 : indexLoop 10 92 0 = some [(93,0)] := by rfl
lemma loop96 : indexLoop 10 96 0 = some [(97,0)] := by rfl

#print axioms loop191
#print axioms loop188
#print axioms loop3
#print axioms loop0
#print axioms loop94
#print axioms loop95
#print axioms loop1
#print axioms loop2
#print axioms loop64
#print axioms loop80
#print axioms loop88
#print axioms loop92
#print axioms loop96
end AspisV8R19.R748FiniteGatherSchedules

namespace AspisV8R19.R748FiniteGatherSchedules
open AspisV8R17
open scoped BigOperators
variable {F : Type*} [CommRing F]
example (half : F) (w : Nat → F) :
    sourceGather half w 95 =
      half*w 94 + half^2*w 92 + half^3*w 88 + half^4*w 80 + half^5*w 64 + half^5*w 96 := by
  rw [sourceGather_powers, loop95]
  simp [List.map_map]
end AspisV8R19.R748FiniteGatherSchedules
