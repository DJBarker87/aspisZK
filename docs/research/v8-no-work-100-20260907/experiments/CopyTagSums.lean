import CopyScatterNodes
namespace AspisV8.CopyTagSums
open AspisV8.CopyScatter
variable {K:Type*} [CommRing K]
theorem coordinate0 (h:Fin 64→K) : (0:K) + h 63 + h 4 = h 4 + h 63 := by
  ring
#print axioms coordinate0
theorem coordinate1 (h:Fin 64→K) : (0:K) + h 57 = h 57 := by
  ring
#print axioms coordinate1
theorem coordinate2 (h:Fin 64→K) : (0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node41 h := by
  simp only [node41_spec] <;> ring
#print axioms coordinate2
theorem coordinate3 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate3
theorem coordinate4 (h:Fin 64→K) : (0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node41 h := by
  simp only [node41_spec] <;> ring
#print axioms coordinate4
theorem coordinate5 (h:Fin 64→K) : (0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node41 h := by
  simp only [node41_spec] <;> ring
#print axioms coordinate5
theorem coordinate6 (h:Fin 64→K) : (0:K) + h 1 + h 2 + h 25 + h 27 + h 28 + h 30 + h 31 + h 0 + h 32 + h 29 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 3 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 = h 27 + node29 h + node51 h + node52 h + node54 h + node55 h := by
  simp only [node29_spec,node51_spec,node52_spec,node54_spec,node55_spec] <;> ring
#print axioms coordinate6
theorem coordinate7 (h:Fin 64→K) : (0:K) + h 0 + h 2 + h 3 + h 28 + h 31 = h 0 + h 28 + node29 h := by
  simp only [node29_spec] <;> ring
#print axioms coordinate7
theorem coordinate8 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate8
theorem coordinate9 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate9
theorem coordinate10 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate10
theorem coordinate11 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate11
theorem coordinate12 (h:Fin 64→K) : (0:K) + h 32 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 = node55 h := by
  simp only [node55_spec] <;> ring
#print axioms coordinate12
theorem coordinate13 (h:Fin 64→K) : (0:K) + h 2 = h 2 := by
  ring
#print axioms coordinate13
theorem coordinate14 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate14
theorem coordinate15 (h:Fin 64→K) : (0:K) + h 2 + h 3 + h 26 + h 28 + h 29 + h 31 + h 32 + h 63 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56 = h 63 + node51 h + node57 h + node58 h := by
  simp only [node51_spec,node57_spec,node58_spec] <;> ring
#print axioms coordinate15
theorem coordinate16 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate16
theorem coordinate17 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate17
theorem coordinate18 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate18
theorem coordinate19 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate19
theorem coordinate20 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate20
theorem coordinate21 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate21
theorem coordinate22 (h:Fin 64→K) : (0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node41 h := by
  simp only [node41_spec] <;> ring
#print axioms coordinate22
theorem coordinate23 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate23
theorem coordinate24 (h:Fin 64→K) : (0:K) + h 1 + h 25 + h 26 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56 = h 26 + node28 h + node58 h := by
  simp only [node28_spec,node58_spec] <;> ring
#print axioms coordinate24
theorem coordinate25 (h:Fin 64→K) : (0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62 = node4 h := by
  simp only [node4_spec] <;> ring
#print axioms coordinate25
theorem coordinate26 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate26
theorem coordinate27 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate27
theorem coordinate28 (h:Fin 64→K) : (0:K) + h 63 = h 63 := by
  ring
#print axioms coordinate28
theorem coordinate29 (h:Fin 64→K) : (0:K) + h 26 + h 33 = h 26 + h 33 := by
  ring
#print axioms coordinate29
def original0 (h:Fin 64→K) : Fin 15→K := ![
(0:K) + h 63 + h 4,
(0:K) + h 57,
(0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 63,
(0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 1 + h 2 + h 25 + h 27 + h 28 + h 30 + h 31 + h 0 + h 32 + h 29 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 3 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55,
(0:K) + h 0 + h 2 + h 3 + h 28 + h 31,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 32 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52,
(0:K) + h 2,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62]
def original15 (h:Fin 64→K) : Fin 15→K := ![
(0:K) + h 2 + h 3 + h 26 + h 28 + h 29 + h 31 + h 32 + h 63 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63 + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 63,
(0:K) + h 1 + h 25 + h 26 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56,
(0:K) + h 57 + h 58 + h 59 + h 60 + h 61 + h 62,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 63,
(0:K) + h 26 + h 33]
def original (h:Fin 64→K) (i:Fin 30) : K :=
  if hh:i.val<15 then original0 h ⟨i.val,hh⟩ else original15 h ⟨i.val-15,by omega⟩
def shared0 (h:Fin 64→K) : Fin 15→K := ![
h 4 + h 63,
h 57,
node41 h,
h 63,
node41 h,
node41 h,
h 27 + node29 h + node51 h + node52 h + node54 h + node55 h,
h 0 + h 28 + node29 h,
node4 h,
node4 h,
node4 h,
node4 h,
node55 h,
h 2,
node4 h]
def shared15 (h:Fin 64→K) : Fin 15→K := ![
h 63 + node51 h + node57 h + node58 h,
node4 h,
h 63,
h 63,
node4 h,
h 63,
h 63,
node41 h,
h 63,
h 26 + node28 h + node58 h,
node4 h,
h 63,
h 63,
h 63,
h 26 + h 33]
def shared (h:Fin 64→K) (i:Fin 30) : K :=
  if hh:i.val<15 then shared0 h ⟨i.val,hh⟩ else shared15 h ⟨i.val-15,by omega⟩
theorem all_tag_sums (h:Fin 64→K) : original h=shared h := by
  funext i
  fin_cases i
  · exact coordinate0 h
  · exact coordinate1 h
  · exact coordinate2 h
  · exact coordinate3 h
  · exact coordinate4 h
  · exact coordinate5 h
  · exact coordinate6 h
  · exact coordinate7 h
  · exact coordinate8 h
  · exact coordinate9 h
  · exact coordinate10 h
  · exact coordinate11 h
  · exact coordinate12 h
  · exact coordinate13 h
  · exact coordinate14 h
  · exact coordinate15 h
  · exact coordinate16 h
  · exact coordinate17 h
  · exact coordinate18 h
  · exact coordinate19 h
  · exact coordinate20 h
  · exact coordinate21 h
  · exact coordinate22 h
  · exact coordinate23 h
  · exact coordinate24 h
  · exact coordinate25 h
  · exact coordinate26 h
  · exact coordinate27 h
  · exact coordinate28 h
  · exact coordinate29 h
#print axioms all_tag_sums
end AspisV8.CopyTagSums
