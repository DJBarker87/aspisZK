import CopyScatterNodes
namespace AspisV8.CopyScatter
variable {K : Type*} [CommRing K]
theorem coordinate30 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) + w 0 * (h 4) = w 0 * (h 4 + h 63) := by
  ring
#print axioms coordinate30
theorem coordinate31 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) = w 0 * (h 57) := by
  ring
#print axioms coordinate31
theorem coordinate32 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node41 h) := by
  simp only [node41_spec] <;> ring
#print axioms coordinate32
theorem coordinate33 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) = w 0 * (h 63) := by
  ring
#print axioms coordinate33
theorem coordinate34 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node41 h) := by
  simp only [node41_spec] <;> ring
#print axioms coordinate34
theorem coordinate35 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node41 h) := by
  simp only [node41_spec] <;> ring
#print axioms coordinate35
theorem coordinate36 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 1) + w 0 * (h 2) + w 0 * (h 25) + w 1 * (h 27) + w 1 * (h 28) + w 0 * (h 30) + w 0 * (h 31) + w 0 * (h 0) + w 1 * (h 32) + w 1 * (h 29) + w 3 * (h 33) + w 4 * (h 34) + w 5 * (h 35) + w 6 * (h 36) + w 7 * (h 37) + w 8 * (h 38) + w 9 * (h 39) + w 10 * (h 40) + w 11 * (h 41) + w 12 * (h 42) + w 13 * (h 43) + w 14 * (h 44) + w 15 * (h 45) + w 16 * (h 46) + w 17 * (h 47) + w 18 * (h 48) + w 19 * (h 49) + w 20 * (h 50) + w 21 * (h 51) + w 22 * (h 52) + w 0 * (h 3) + w 0 * (h 4) + w 0 * (h 5) + w 0 * (h 6) + w 0 * (h 7) + w 0 * (h 8) + w 0 * (h 9) + w 0 * (h 10) + w 0 * (h 11) + w 0 * (h 12) + w 0 * (h 13) + w 0 * (h 14) + w 0 * (h 15) + w 0 * (h 16) + w 0 * (h 17) + w 0 * (h 18) + w 0 * (h 19) + w 0 * (h 20) + w 0 * (h 21) + w 0 * (h 22) + w 0 * (h 23) + w 0 * (h 24) + w 0 * (h 54) + w 0 * (h 55) = w 0 * (node29 h + node52 h + node54 h) + w 1 * (h 27 + h 32 + node51 h) + w 3 * (h 33) + w 4 * (h 34) + w 5 * (h 35) + w 6 * (h 36) + w 7 * (h 37) + w 8 * (h 38) + w 9 * (h 39) + w 10 * (h 40) + w 11 * (h 41) + w 12 * (h 42) + w 13 * (h 43) + w 14 * (h 44) + w 15 * (h 45) + w 16 * (h 46) + w 17 * (h 47) + w 18 * (h 48) + w 19 * (h 49) + w 20 * (h 50) + w 21 * (h 51) + w 22 * (h 52) := by
  simp only [node29_spec,node51_spec,node52_spec,node54_spec] <;> ring
#print axioms coordinate36
theorem coordinate37 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 0) + w 0 * (h 2) + w 0 * (h 3) + w 1 * (h 28) + w 0 * (h 31) = w 0 * (h 0 + node29 h) + w 1 * (h 28) := by
  simp only [node29_spec] <;> ring
#print axioms coordinate37
theorem coordinate38 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate38
theorem coordinate39 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate39
theorem coordinate40 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate40
theorem coordinate41 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate41
theorem coordinate42 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 2 * (h 32) + w 23 * (h 33) + w 24 * (h 34) + w 25 * (h 35) + w 26 * (h 36) + w 27 * (h 37) + w 28 * (h 38) + w 29 * (h 39) + w 30 * (h 40) + w 31 * (h 41) + w 32 * (h 42) + w 33 * (h 43) + w 34 * (h 44) + w 35 * (h 45) + w 36 * (h 46) + w 37 * (h 47) + w 38 * (h 48) + w 39 * (h 49) + w 40 * (h 50) + w 41 * (h 51) + w 42 * (h 52) = w 2 * (h 32) + w 23 * (h 33) + w 24 * (h 34) + w 25 * (h 35) + w 26 * (h 36) + w 27 * (h 37) + w 28 * (h 38) + w 29 * (h 39) + w 30 * (h 40) + w 31 * (h 41) + w 32 * (h 42) + w 33 * (h 43) + w 34 * (h 44) + w 35 * (h 45) + w 36 * (h 46) + w 37 * (h 47) + w 38 * (h 48) + w 39 * (h 49) + w 40 * (h 50) + w 41 * (h 51) + w 42 * (h 52) := by
  ring
#print axioms coordinate42
theorem coordinate43 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 2) = w 0 * (h 2) := by
  ring
#print axioms coordinate43
theorem coordinate44 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate44
theorem coordinate45 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 2) + w 0 * (h 3) + w 0 * (h 26) + w 1 * (h 28) + w 1 * (h 29) + w 0 * (h 31) + w 0 * (h 32) + w 0 * (h 63) + w 0 * (h 33) + w 23 * (h 34) + w 24 * (h 35) + w 25 * (h 36) + w 26 * (h 37) + w 27 * (h 38) + w 28 * (h 39) + w 29 * (h 40) + w 30 * (h 41) + w 31 * (h 42) + w 32 * (h 43) + w 33 * (h 44) + w 34 * (h 45) + w 35 * (h 46) + w 36 * (h 47) + w 37 * (h 48) + w 38 * (h 49) + w 39 * (h 50) + w 40 * (h 51) + w 41 * (h 52) + w 42 * (h 53) + w 0 * (h 4) + w 0 * (h 5) + w 0 * (h 6) + w 0 * (h 7) + w 0 * (h 8) + w 0 * (h 9) + w 0 * (h 10) + w 0 * (h 11) + w 0 * (h 12) + w 0 * (h 13) + w 0 * (h 14) + w 0 * (h 15) + w 0 * (h 16) + w 0 * (h 17) + w 0 * (h 18) + w 0 * (h 19) + w 0 * (h 20) + w 0 * (h 21) + w 0 * (h 22) + w 0 * (h 23) + w 0 * (h 24) + w 0 * (h 54) + w 0 * (h 55) + w 0 * (h 56) = w 0 * (h 33 + h 63 + node40 h + node57 h) + w 1 * (node51 h) + w 23 * (h 34) + w 24 * (h 35) + w 25 * (h 36) + w 26 * (h 37) + w 27 * (h 38) + w 28 * (h 39) + w 29 * (h 40) + w 30 * (h 41) + w 31 * (h 42) + w 32 * (h 43) + w 33 * (h 44) + w 34 * (h 45) + w 35 * (h 46) + w 36 * (h 47) + w 37 * (h 48) + w 38 * (h 49) + w 39 * (h 50) + w 40 * (h 51) + w 41 * (h 52) + w 42 * (h 53) := by
  simp only [node40_spec,node51_spec,node57_spec] <;> ring
#print axioms coordinate45
theorem coordinate46 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate46
theorem coordinate47 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 1 * (h 63) = w 1 * (h 63) := by
  ring
#print axioms coordinate47
theorem coordinate48 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) = w 0 * (h 63) := by
  ring
#print axioms coordinate48
theorem coordinate49 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node4 h) := by
  simp only [node4_spec] <;> ring
#print axioms coordinate49
theorem coordinate50 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) = w 0 * (h 63) := by
  ring
#print axioms coordinate50
theorem coordinate51 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) = w 0 * (h 63) := by
  ring
#print axioms coordinate51
theorem coordinate52 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 63) + w 0 * (h 57) + w 0 * (h 58) + w 0 * (h 59) + w 0 * (h 60) + w 0 * (h 61) + w 0 * (h 62) = w 0 * (node41 h) := by
  simp only [node41_spec] <;> ring
#print axioms coordinate52
theorem coordinate53 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 1 * (h 63) = w 1 * (h 63) := by
  ring
#print axioms coordinate53
theorem coordinate54 (h:Fin 64→K) (w:Fin 43→K) :
    (0:K) + w 0 * (h 1) + w 0 * (h 25) + w 0 * (h 26) + w 1 * (h 33) + w 3 * (h 34) + w 4 * (h 35) + w 5 * (h 36) + w 6 * (h 37) + w 7 * (h 38) + w 8 * (h 39) + w 9 * (h 40) + w 10 * (h 41) + w 11 * (h 42) + w 12 * (h 43) + w 13 * (h 44) + w 14 * (h 45) + w 15 * (h 46) + w 16 * (h 47) + w 17 * (h 48) + w 18 * (h 49) + w 19 * (h 50) + w 20 * (h 51) + w 21 * (h 52) + w 22 * (h 53) + w 0 * (h 4) + w 0 * (h 5) + w 0 * (h 6) + w 0 * (h 7) + w 0 * (h 8) + w 0 * (h 9) + w 0 * (h 10) + w 0 * (h 11) + w 0 * (h 12) + w 0 * (h 13) + w 0 * (h 14) + w 0 * (h 15) + w 0 * (h 16) + w 0 * (h 17) + w 0 * (h 18) + w 0 * (h 19) + w 0 * (h 20) + w 0 * (h 21) + w 0 * (h 22) + w 0 * (h 23) + w 0 * (h 24) + w 0 * (h 54) + w 0 * (h 55) + w 0 * (h 56) = w 0 * (h 26 + node28 h + node40 h) + w 1 * (h 33) + w 3 * (h 34) + w 4 * (h 35) + w 5 * (h 36) + w 6 * (h 37) + w 7 * (h 38) + w 8 * (h 39) + w 9 * (h 40) + w 10 * (h 41) + w 11 * (h 42) + w 12 * (h 43) + w 13 * (h 44) + w 14 * (h 45) + w 15 * (h 46) + w 16 * (h 47) + w 17 * (h 48) + w 18 * (h 49) + w 19 * (h 50) + w 20 * (h 51) + w 21 * (h 52) + w 22 * (h 53) := by
  simp only [node28_spec,node40_spec] <;> ring
#print axioms coordinate54
end AspisV8.CopyScatter
