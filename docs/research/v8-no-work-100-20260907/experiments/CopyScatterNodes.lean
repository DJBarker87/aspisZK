import Mathlib.Tactic
-- Frozen table SHA256 cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50
namespace AspisV8.CopyScatter
variable {K : Type*} [CommRing K]
theorem bool_weight (b:Bool) (x:K) : (if b then x else 0)=(if b then (1:K) else 0)*x := by cases b <;> simp
theorem zero_cell : (0:K)=0 := Eq.refl 0
def node0 (h:Fin 64→K) : K := h 57 + h 58
theorem node0_spec (h:Fin 64→K) : node0 h = h 57 + h 58 := by
  simp only [node0] <;> ring
def node1 (h:Fin 64→K) : K := h 59 + h 60
theorem node1_spec (h:Fin 64→K) : node1 h = h 59 + h 60 := by
  simp only [node1] <;> ring
def node2 (h:Fin 64→K) : K := h 61 + h 62
theorem node2_spec (h:Fin 64→K) : node2 h = h 61 + h 62 := by
  simp only [node2] <;> ring
def node3 (h:Fin 64→K) : K := node0 h + node1 h
theorem node3_spec (h:Fin 64→K) : node3 h = h 57 + h 58 + h 59 + h 60 := by
  simp only [node3 ,node0_spec,node1_spec] <;> ring
def node4 (h:Fin 64→K) : K := node2 h + node3 h
theorem node4_spec (h:Fin 64→K) : node4 h = h 57 + h 58 + h 59 + h 60 + h 61 + h 62 := by
  simp only [node4 ,node2_spec,node3_spec] <;> ring
def node5 (h:Fin 64→K) : K := h 4 + h 5
theorem node5_spec (h:Fin 64→K) : node5 h = h 4 + h 5 := by
  simp only [node5] <;> ring
def node6 (h:Fin 64→K) : K := h 6 + h 7
theorem node6_spec (h:Fin 64→K) : node6 h = h 6 + h 7 := by
  simp only [node6] <;> ring
def node7 (h:Fin 64→K) : K := h 8 + h 9
theorem node7_spec (h:Fin 64→K) : node7 h = h 8 + h 9 := by
  simp only [node7] <;> ring
def node8 (h:Fin 64→K) : K := h 10 + h 11
theorem node8_spec (h:Fin 64→K) : node8 h = h 10 + h 11 := by
  simp only [node8] <;> ring
def node9 (h:Fin 64→K) : K := h 12 + h 13
theorem node9_spec (h:Fin 64→K) : node9 h = h 12 + h 13 := by
  simp only [node9] <;> ring
def node10 (h:Fin 64→K) : K := h 14 + h 15
theorem node10_spec (h:Fin 64→K) : node10 h = h 14 + h 15 := by
  simp only [node10] <;> ring
def node11 (h:Fin 64→K) : K := h 16 + h 17
theorem node11_spec (h:Fin 64→K) : node11 h = h 16 + h 17 := by
  simp only [node11] <;> ring
def node12 (h:Fin 64→K) : K := h 18 + h 19
theorem node12_spec (h:Fin 64→K) : node12 h = h 18 + h 19 := by
  simp only [node12] <;> ring
def node13 (h:Fin 64→K) : K := h 20 + h 21
theorem node13_spec (h:Fin 64→K) : node13 h = h 20 + h 21 := by
  simp only [node13] <;> ring
def node14 (h:Fin 64→K) : K := h 22 + h 23
theorem node14_spec (h:Fin 64→K) : node14 h = h 22 + h 23 := by
  simp only [node14] <;> ring
def node15 (h:Fin 64→K) : K := h 24 + h 54
theorem node15_spec (h:Fin 64→K) : node15 h = h 24 + h 54 := by
  simp only [node15] <;> ring
def node16 (h:Fin 64→K) : K := h 55 + node5 h
theorem node16_spec (h:Fin 64→K) : node16 h = h 4 + h 5 + h 55 := by
  simp only [node16 ,node5_spec] <;> ring
def node17 (h:Fin 64→K) : K := node6 h + node7 h
theorem node17_spec (h:Fin 64→K) : node17 h = h 6 + h 7 + h 8 + h 9 := by
  simp only [node17 ,node6_spec,node7_spec] <;> ring
def node18 (h:Fin 64→K) : K := node8 h + node9 h
theorem node18_spec (h:Fin 64→K) : node18 h = h 10 + h 11 + h 12 + h 13 := by
  simp only [node18 ,node8_spec,node9_spec] <;> ring
def node19 (h:Fin 64→K) : K := node10 h + node11 h
theorem node19_spec (h:Fin 64→K) : node19 h = h 14 + h 15 + h 16 + h 17 := by
  simp only [node19 ,node10_spec,node11_spec] <;> ring
def node20 (h:Fin 64→K) : K := node12 h + node13 h
theorem node20_spec (h:Fin 64→K) : node20 h = h 18 + h 19 + h 20 + h 21 := by
  simp only [node20 ,node12_spec,node13_spec] <;> ring
def node21 (h:Fin 64→K) : K := node14 h + node15 h
theorem node21_spec (h:Fin 64→K) : node21 h = h 22 + h 23 + h 24 + h 54 := by
  simp only [node21 ,node14_spec,node15_spec] <;> ring
def node22 (h:Fin 64→K) : K := node16 h + node17 h
theorem node22_spec (h:Fin 64→K) : node22 h = h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 55 := by
  simp only [node22 ,node16_spec,node17_spec] <;> ring
def node23 (h:Fin 64→K) : K := node18 h + node19 h
theorem node23_spec (h:Fin 64→K) : node23 h = h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 := by
  simp only [node23 ,node18_spec,node19_spec] <;> ring
def node24 (h:Fin 64→K) : K := node20 h + node21 h
theorem node24_spec (h:Fin 64→K) : node24 h = h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 := by
  simp only [node24 ,node20_spec,node21_spec] <;> ring
def node25 (h:Fin 64→K) : K := node22 h + node23 h
theorem node25_spec (h:Fin 64→K) : node25 h = h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 55 := by
  simp only [node25 ,node22_spec,node23_spec] <;> ring
def node26 (h:Fin 64→K) : K := node24 h + node25 h
theorem node26_spec (h:Fin 64→K) : node26 h = h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 := by
  simp only [node26 ,node24_spec,node25_spec] <;> ring
def node27 (h:Fin 64→K) : K := h 2 + h 31
theorem node27_spec (h:Fin 64→K) : node27 h = h 2 + h 31 := by
  simp only [node27] <;> ring
def node28 (h:Fin 64→K) : K := h 1 + h 25
theorem node28_spec (h:Fin 64→K) : node28 h = h 1 + h 25 := by
  simp only [node28] <;> ring
def node29 (h:Fin 64→K) : K := h 3 + node27 h
theorem node29_spec (h:Fin 64→K) : node29 h = h 2 + h 3 + h 31 := by
  simp only [node29 ,node27_spec] <;> ring
def node30 (h:Fin 64→K) : K := h 33 + h 34
theorem node30_spec (h:Fin 64→K) : node30 h = h 33 + h 34 := by
  simp only [node30] <;> ring
def node31 (h:Fin 64→K) : K := h 35 + h 36
theorem node31_spec (h:Fin 64→K) : node31 h = h 35 + h 36 := by
  simp only [node31] <;> ring
def node32 (h:Fin 64→K) : K := h 37 + h 38
theorem node32_spec (h:Fin 64→K) : node32 h = h 37 + h 38 := by
  simp only [node32] <;> ring
def node33 (h:Fin 64→K) : K := h 39 + h 40
theorem node33_spec (h:Fin 64→K) : node33 h = h 39 + h 40 := by
  simp only [node33] <;> ring
def node34 (h:Fin 64→K) : K := h 41 + h 42
theorem node34_spec (h:Fin 64→K) : node34 h = h 41 + h 42 := by
  simp only [node34] <;> ring
def node35 (h:Fin 64→K) : K := h 43 + h 44
theorem node35_spec (h:Fin 64→K) : node35 h = h 43 + h 44 := by
  simp only [node35] <;> ring
def node36 (h:Fin 64→K) : K := h 45 + h 46
theorem node36_spec (h:Fin 64→K) : node36 h = h 45 + h 46 := by
  simp only [node36] <;> ring
def node37 (h:Fin 64→K) : K := h 47 + h 48
theorem node37_spec (h:Fin 64→K) : node37 h = h 47 + h 48 := by
  simp only [node37] <;> ring
def node38 (h:Fin 64→K) : K := h 49 + h 50
theorem node38_spec (h:Fin 64→K) : node38 h = h 49 + h 50 := by
  simp only [node38] <;> ring
def node39 (h:Fin 64→K) : K := h 51 + h 52
theorem node39_spec (h:Fin 64→K) : node39 h = h 51 + h 52 := by
  simp only [node39] <;> ring
def node40 (h:Fin 64→K) : K := h 56 + node26 h
theorem node40_spec (h:Fin 64→K) : node40 h = h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 + h 56 := by
  simp only [node40 ,node26_spec] <;> ring
def node41 (h:Fin 64→K) : K := h 63 + node4 h
theorem node41_spec (h:Fin 64→K) : node41 h = h 57 + h 58 + h 59 + h 60 + h 61 + h 62 + h 63 := by
  simp only [node41 ,node4_spec] <;> ring
def node42 (h:Fin 64→K) : K := node30 h + node31 h
theorem node42_spec (h:Fin 64→K) : node42 h = h 33 + h 34 + h 35 + h 36 := by
  simp only [node42 ,node30_spec,node31_spec] <;> ring
def node43 (h:Fin 64→K) : K := node32 h + node33 h
theorem node43_spec (h:Fin 64→K) : node43 h = h 37 + h 38 + h 39 + h 40 := by
  simp only [node43 ,node32_spec,node33_spec] <;> ring
def node44 (h:Fin 64→K) : K := node34 h + node35 h
theorem node44_spec (h:Fin 64→K) : node44 h = h 41 + h 42 + h 43 + h 44 := by
  simp only [node44 ,node34_spec,node35_spec] <;> ring
def node45 (h:Fin 64→K) : K := node36 h + node37 h
theorem node45_spec (h:Fin 64→K) : node45 h = h 45 + h 46 + h 47 + h 48 := by
  simp only [node45 ,node36_spec,node37_spec] <;> ring
def node46 (h:Fin 64→K) : K := node38 h + node39 h
theorem node46_spec (h:Fin 64→K) : node46 h = h 49 + h 50 + h 51 + h 52 := by
  simp only [node46 ,node38_spec,node39_spec] <;> ring
def node47 (h:Fin 64→K) : K := node42 h + node43 h
theorem node47_spec (h:Fin 64→K) : node47 h = h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 := by
  simp only [node47 ,node42_spec,node43_spec] <;> ring
def node48 (h:Fin 64→K) : K := node44 h + node45 h
theorem node48_spec (h:Fin 64→K) : node48 h = h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 := by
  simp only [node48 ,node44_spec,node45_spec] <;> ring
def node49 (h:Fin 64→K) : K := node46 h + node47 h
theorem node49_spec (h:Fin 64→K) : node49 h = h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 49 + h 50 + h 51 + h 52 := by
  simp only [node49 ,node46_spec,node47_spec] <;> ring
def node50 (h:Fin 64→K) : K := node48 h + node49 h
theorem node50_spec (h:Fin 64→K) : node50 h = h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 := by
  simp only [node50 ,node48_spec,node49_spec] <;> ring
def node51 (h:Fin 64→K) : K := h 28 + h 29
theorem node51_spec (h:Fin 64→K) : node51 h = h 28 + h 29 := by
  simp only [node51] <;> ring
def node52 (h:Fin 64→K) : K := h 0 + node26 h
theorem node52_spec (h:Fin 64→K) : node52 h = h 0 + h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 54 + h 55 := by
  simp only [node52 ,node26_spec] <;> ring
def node53 (h:Fin 64→K) : K := h 26 + h 32
theorem node53_spec (h:Fin 64→K) : node53 h = h 26 + h 32 := by
  simp only [node53] <;> ring
def node54 (h:Fin 64→K) : K := h 30 + node28 h
theorem node54_spec (h:Fin 64→K) : node54 h = h 1 + h 25 + h 30 := by
  simp only [node54 ,node28_spec] <;> ring
def node55 (h:Fin 64→K) : K := h 32 + node50 h
theorem node55_spec (h:Fin 64→K) : node55 h = h 32 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 := by
  simp only [node55 ,node50_spec] <;> ring
def node56 (h:Fin 64→K) : K := h 53 + node40 h
theorem node56_spec (h:Fin 64→K) : node56 h = h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 53 + h 54 + h 55 + h 56 := by
  simp only [node56 ,node40_spec] <;> ring
def node57 (h:Fin 64→K) : K := node29 h + node53 h
theorem node57_spec (h:Fin 64→K) : node57 h = h 2 + h 3 + h 26 + h 31 + h 32 := by
  simp only [node57 ,node29_spec,node53_spec] <;> ring
def node58 (h:Fin 64→K) : K := node50 h + node56 h
theorem node58_spec (h:Fin 64→K) : node58 h = h 4 + h 5 + h 6 + h 7 + h 8 + h 9 + h 10 + h 11 + h 12 + h 13 + h 14 + h 15 + h 16 + h 17 + h 18 + h 19 + h 20 + h 21 + h 22 + h 23 + h 24 + h 33 + h 34 + h 35 + h 36 + h 37 + h 38 + h 39 + h 40 + h 41 + h 42 + h 43 + h 44 + h 45 + h 46 + h 47 + h 48 + h 49 + h 50 + h 51 + h 52 + h 53 + h 54 + h 55 + h 56 := by
  simp only [node58 ,node50_spec,node56_spec] <;> ring
#print axioms bool_weight
#print axioms node0_spec
#print axioms node1_spec
#print axioms node2_spec
#print axioms node3_spec
#print axioms node4_spec
#print axioms node5_spec
#print axioms node6_spec
#print axioms node7_spec
#print axioms node8_spec
#print axioms node9_spec
#print axioms node10_spec
#print axioms node11_spec
#print axioms node12_spec
#print axioms node13_spec
#print axioms node14_spec
#print axioms node15_spec
#print axioms node16_spec
#print axioms node17_spec
#print axioms node18_spec
#print axioms node19_spec
#print axioms node20_spec
#print axioms node21_spec
#print axioms node22_spec
#print axioms node23_spec
#print axioms node24_spec
#print axioms node25_spec
#print axioms node26_spec
#print axioms node27_spec
#print axioms node28_spec
#print axioms node29_spec
#print axioms node30_spec
#print axioms node31_spec
#print axioms node32_spec
#print axioms node33_spec
#print axioms node34_spec
#print axioms node35_spec
#print axioms node36_spec
#print axioms node37_spec
#print axioms node38_spec
#print axioms node39_spec
#print axioms node40_spec
#print axioms node41_spec
#print axioms node42_spec
#print axioms node43_spec
#print axioms node44_spec
#print axioms node45_spec
#print axioms node46_spec
#print axioms node47_spec
#print axioms node48_spec
#print axioms node49_spec
#print axioms node50_spec
#print axioms node51_spec
#print axioms node52_spec
#print axioms node53_spec
#print axioms node54_spec
#print axioms node55_spec
#print axioms node56_spec
#print axioms node57_spec
#print axioms node58_spec
end AspisV8.CopyScatter
