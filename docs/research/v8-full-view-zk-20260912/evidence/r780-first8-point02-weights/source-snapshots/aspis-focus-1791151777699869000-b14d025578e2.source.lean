import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R772Point02DualLeaves
import AspisV8R19.R772Point02DualLeavesChunk00
import AspisV8R19.R772Point02DualLeavesChunk01
import AspisV8R19.R772Point02DualLeavesChunk02
import AspisV8R19.R772Point02DualLeavesChunk03
import AspisV8R19.R772Point02DualLeavesChunk04
import AspisV8R19.R772Point02DualLeavesChunk05
import AspisV8R19.R772Point02DualLeavesChunk06
import AspisV8R19.R772Point02DualLeavesChunk07
import AspisV8R19.R772Point02DualLeavesChunk08
import AspisV8R19.R772Point02DualLeavesChunk09
import AspisV8R19.R772Point02DualLeavesChunk10
import AspisV8R19.R772Point02DualLeavesChunk11
import AspisV8R19.R772Point02DualLeavesChunk12
import AspisV8R19.R772Point02DualLeavesChunk13
import AspisV8R19.R772Point02DualLeavesChunk14
import AspisV8R19.R772Point02DualLeavesChunk15
import AspisV8R19.R772Point02DualLeavesChunk16
import AspisV8R19.R772Point02DualLeavesChunk17
import AspisV8R19.R772Point02DualLeavesChunk18
import AspisV8R19.R772Point02DualLeavesChunk19
import AspisV8R19.R772Point02DualLeavesChunk20
import AspisV8R19.R772Point02DualLeavesChunk21
import AspisV8R19.R772Point02DualLeavesChunk22
import AspisV8R19.R772Point02DualLeavesChunk23
import AspisV8R19.R772Point02DualLeavesChunk24
import AspisV8R19.R772Point02DualLeavesChunk25
import AspisV8R19.R772Point02DualLeavesChunk26
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk28
import AspisV8R19.R772Point02DualLeavesChunk29
import AspisV8R19.R772Point02DualLeavesChunk30
import AspisV8R19.R772Point02DualLeavesChunk31
import AspisV8R19.R772Point02DualLeavesChunk32

namespace AspisV8R19.R780Point02WeightShared
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem w0_at (i : Fin 1024) : w0 i.val = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) i := by
  simp [w0, extendFin1024, i.isLt]
#print axioms w0_at

theorem w2_at (i : Fin 1024) : w2 i.val = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) i := by
  simp [w2, extendFin1024, i.isLt]
#print axioms w2_at

theorem w0_leaf_0 : w0 0 = 0 := by
  have hpos : order.symm (14 : Fin 1024) = (0 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeaves.point0_guard14_transport_zero (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (0 : Fin 1024))]
  exact hs

#print axioms w0_leaf_0
theorem w0_leaf_1 : w0 1 = 0 := by
  have hpos : order.symm (15 : Fin 1024) = (1 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_15 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1
theorem w0_leaf_2 : w0 2 = 0 := by
  have hpos : order.symm (30 : Fin 1024) = (2 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_30 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (2 : Fin 1024))]
  exact hs

#print axioms w0_leaf_2
theorem w0_leaf_3 : w0 3 = 0 := by
  have hpos : order.symm (31 : Fin 1024) = (3 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_31 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (3 : Fin 1024))]
  exact hs

#print axioms w0_leaf_3
theorem w0_leaf_4 : w0 4 = 0 := by
  have hpos : order.symm (46 : Fin 1024) = (4 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_46 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (4 : Fin 1024))]
  exact hs

#print axioms w0_leaf_4
theorem w0_leaf_5 : w0 5 = 0 := by
  have hpos : order.symm (47 : Fin 1024) = (5 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_47 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (5 : Fin 1024))]
  exact hs

#print axioms w0_leaf_5
theorem w0_leaf_6 : w0 6 = 0 := by
  have hpos : order.symm (62 : Fin 1024) = (6 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_62 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (6 : Fin 1024))]
  exact hs

#print axioms w0_leaf_6
theorem w0_leaf_64 : w0 64 = 0 := by
  have hpos : order.symm (526 : Fin 1024) = (64 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_526 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (64 : Fin 1024))]
  exact hs

#print axioms w0_leaf_64
theorem w0_leaf_65 : w0 65 = 0 := by
  have hpos : order.symm (527 : Fin 1024) = (65 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_527 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (65 : Fin 1024))]
  exact hs

#print axioms w0_leaf_65
theorem w0_leaf_66 : w0 66 = 0 := by
  have hpos : order.symm (542 : Fin 1024) = (66 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_542 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (66 : Fin 1024))]
  exact hs

#print axioms w0_leaf_66
theorem w0_leaf_80 : w0 80 = 0 := by
  have hpos : order.symm (654 : Fin 1024) = (80 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_654 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (80 : Fin 1024))]
  exact hs

#print axioms w0_leaf_80
theorem w0_leaf_81 : w0 81 = 0 := by
  have hpos : order.symm (655 : Fin 1024) = (81 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_655 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (81 : Fin 1024))]
  exact hs

#print axioms w0_leaf_81
theorem w0_leaf_82 : w0 82 = 0 := by
  have hpos : order.symm (670 : Fin 1024) = (82 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_670 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (82 : Fin 1024))]
  exact hs

#print axioms w0_leaf_82
theorem w0_leaf_88 : w0 88 = 0 := by
  have hpos : order.symm (718 : Fin 1024) = (88 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_718 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (88 : Fin 1024))]
  exact hs

#print axioms w0_leaf_88
theorem w0_leaf_89 : w0 89 = 0 := by
  have hpos : order.symm (719 : Fin 1024) = (89 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_719 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (89 : Fin 1024))]
  exact hs

#print axioms w0_leaf_89
theorem w0_leaf_90 : w0 90 = 0 := by
  have hpos : order.symm (734 : Fin 1024) = (90 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_734 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (90 : Fin 1024))]
  exact hs

#print axioms w0_leaf_90
theorem w0_leaf_92 : w0 92 = 0 := by
  have hpos : order.symm (750 : Fin 1024) = (92 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_750 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (92 : Fin 1024))]
  exact hs

#print axioms w0_leaf_92
theorem w0_leaf_93 : w0 93 = 0 := by
  have hpos : order.symm (751 : Fin 1024) = (93 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_751 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (93 : Fin 1024))]
  exact hs

#print axioms w0_leaf_93
theorem w0_leaf_94 : w0 94 = 0 := by
  have hpos : order.symm (766 : Fin 1024) = (94 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_766 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (94 : Fin 1024))]
  exact hs

#print axioms w0_leaf_94
theorem w0_leaf_95 : w0 95 = 0 := by
  have hpos : order.symm (767 : Fin 1024) = (95 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_767 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (95 : Fin 1024))]
  exact hs

#print axioms w0_leaf_95
theorem w0_leaf_96 : w0 96 = 0 := by
  have hpos : order.symm (782 : Fin 1024) = (96 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_782 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (96 : Fin 1024))]
  exact hs

#print axioms w0_leaf_96
theorem w0_leaf_97 : w0 97 = 0 := by
  have hpos : order.symm (783 : Fin 1024) = (97 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_783 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (97 : Fin 1024))]
  exact hs

#print axioms w0_leaf_97
theorem w0_leaf_98 : w0 98 = 0 := by
  have hpos : order.symm (798 : Fin 1024) = (98 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_798 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (98 : Fin 1024))]
  exact hs

#print axioms w0_leaf_98
theorem w0_leaf_99 : w0 99 = 0 := by
  have hpos : order.symm (799 : Fin 1024) = (99 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_799 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (99 : Fin 1024))]
  exact hs

#print axioms w0_leaf_99
theorem w0_leaf_100 : w0 100 = 0 := by
  have hpos : order.symm (814 : Fin 1024) = (100 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_814 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (100 : Fin 1024))]
  exact hs

#print axioms w0_leaf_100
theorem w0_leaf_101 : w0 101 = 0 := by
  have hpos : order.symm (815 : Fin 1024) = (101 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_815 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (101 : Fin 1024))]
  exact hs

#print axioms w0_leaf_101
theorem w0_leaf_102 : w0 102 = 0 := by
  have hpos : order.symm (830 : Fin 1024) = (102 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_830 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (102 : Fin 1024))]
  exact hs

#print axioms w0_leaf_102
theorem w0_leaf_105 : w0 105 = 0 := by
  have hpos : order.symm (847 : Fin 1024) = (105 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_847 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (105 : Fin 1024))]
  exact hs

#print axioms w0_leaf_105
theorem w0_leaf_106 : w0 106 = 0 := by
  have hpos : order.symm (862 : Fin 1024) = (106 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_862 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (106 : Fin 1024))]
  exact hs

#print axioms w0_leaf_106
theorem w0_leaf_108 : w0 108 = 0 := by
  have hpos : order.symm (878 : Fin 1024) = (108 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_878 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (108 : Fin 1024))]
  exact hs

#print axioms w0_leaf_108
theorem w0_leaf_109 : w0 109 = 0 := by
  have hpos : order.symm (879 : Fin 1024) = (109 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_879 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (109 : Fin 1024))]
  exact hs

#print axioms w0_leaf_109
theorem w0_leaf_110 : w0 110 = 0 := by
  have hpos : order.symm (894 : Fin 1024) = (110 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_894 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (110 : Fin 1024))]
  exact hs

#print axioms w0_leaf_110
theorem w0_leaf_111 : w0 111 = 0 := by
  have hpos : order.symm (895 : Fin 1024) = (111 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_895 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (111 : Fin 1024))]
  exact hs

#print axioms w0_leaf_111
theorem w0_leaf_112 : w0 112 = 0 := by
  have hpos : order.symm (910 : Fin 1024) = (112 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_910 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (112 : Fin 1024))]
  exact hs

#print axioms w0_leaf_112
theorem w0_leaf_113 : w0 113 = 0 := by
  have hpos : order.symm (911 : Fin 1024) = (113 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_911 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (113 : Fin 1024))]
  exact hs

#print axioms w0_leaf_113
theorem w0_leaf_114 : w0 114 = 0 := by
  have hpos : order.symm (926 : Fin 1024) = (114 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_926 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (114 : Fin 1024))]
  exact hs

#print axioms w0_leaf_114
theorem w0_leaf_115 : w0 115 = 0 := by
  have hpos : order.symm (927 : Fin 1024) = (115 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_927 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (115 : Fin 1024))]
  exact hs

#print axioms w0_leaf_115
theorem w0_leaf_116 : w0 116 = 0 := by
  have hpos : order.symm (942 : Fin 1024) = (116 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_942 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (116 : Fin 1024))]
  exact hs

#print axioms w0_leaf_116
theorem w0_leaf_117 : w0 117 = 0 := by
  have hpos : order.symm (943 : Fin 1024) = (117 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_943 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (117 : Fin 1024))]
  exact hs

#print axioms w0_leaf_117
theorem w0_leaf_118 : w0 118 = 0 := by
  have hpos : order.symm (958 : Fin 1024) = (118 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_958 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (118 : Fin 1024))]
  exact hs

#print axioms w0_leaf_118
theorem w0_leaf_119 : w0 119 = 0 := by
  have hpos : order.symm (959 : Fin 1024) = (119 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_959 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (119 : Fin 1024))]
  exact hs

#print axioms w0_leaf_119
theorem w0_leaf_120 : w0 120 = 0 := by
  have hpos : order.symm (974 : Fin 1024) = (120 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_974 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (120 : Fin 1024))]
  exact hs

#print axioms w0_leaf_120
theorem w0_leaf_121 : w0 121 = 0 := by
  have hpos : order.symm (975 : Fin 1024) = (121 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_975 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (121 : Fin 1024))]
  exact hs

#print axioms w0_leaf_121
theorem w0_leaf_122 : w0 122 = 0 := by
  have hpos : order.symm (990 : Fin 1024) = (122 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_990 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (122 : Fin 1024))]
  exact hs

#print axioms w0_leaf_122
theorem w0_leaf_123 : w0 123 = 0 := by
  have hpos : order.symm (991 : Fin 1024) = (123 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_991 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (123 : Fin 1024))]
  exact hs

#print axioms w0_leaf_123
theorem w0_leaf_124 : w0 124 = 0 := by
  have hpos : order.symm (1006 : Fin 1024) = (124 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_1006 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (124 : Fin 1024))]
  exact hs

#print axioms w0_leaf_124
theorem w0_leaf_125 : w0 125 = 0 := by
  have hpos : order.symm (1007 : Fin 1024) = (125 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_1007 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (125 : Fin 1024))]
  exact hs

#print axioms w0_leaf_125
theorem w0_leaf_126 : w0 126 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (993 : Fin 1024) = (126 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_993 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (126 : Fin 1024))]
  exact hs

#print axioms w0_leaf_126
theorem w0_leaf_127 : w0 127 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (1009 : Fin 1024) = (127 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_1009 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (127 : Fin 1024))]
  exact hs

#print axioms w0_leaf_127
theorem w0_leaf_128 : w0 128 = 0 := by
  have hpos : order.symm (12 : Fin 1024) = (128 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_12 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (128 : Fin 1024))]
  exact hs

#print axioms w0_leaf_128
theorem w0_leaf_129 : w0 129 = 0 := by
  have hpos : order.symm (13 : Fin 1024) = (129 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_13 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (129 : Fin 1024))]
  exact hs

#print axioms w0_leaf_129
theorem w0_leaf_130 : w0 130 = 0 := by
  have hpos : order.symm (28 : Fin 1024) = (130 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_28 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (130 : Fin 1024))]
  exact hs

#print axioms w0_leaf_130
theorem w0_leaf_131 : w0 131 = 0 := by
  have hpos : order.symm (29 : Fin 1024) = (131 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_29 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (131 : Fin 1024))]
  exact hs

#print axioms w0_leaf_131
theorem w0_leaf_132 : w0 132 = 0 := by
  have hpos : order.symm (44 : Fin 1024) = (132 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_44 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (132 : Fin 1024))]
  exact hs

#print axioms w0_leaf_132
theorem w0_leaf_133 : w0 133 = 0 := by
  have hpos : order.symm (45 : Fin 1024) = (133 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_45 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (133 : Fin 1024))]
  exact hs

#print axioms w0_leaf_133
theorem w0_leaf_134 : w0 134 = 0 := by
  have hpos : order.symm (60 : Fin 1024) = (134 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_60 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (134 : Fin 1024))]
  exact hs

#print axioms w0_leaf_134
theorem w0_leaf_135 : w0 135 = 0 := by
  have hpos : order.symm (61 : Fin 1024) = (135 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_61 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (135 : Fin 1024))]
  exact hs

#print axioms w0_leaf_135
theorem w0_leaf_136 : w0 136 = 0 := by
  have hpos : order.symm (76 : Fin 1024) = (136 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_76 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (136 : Fin 1024))]
  exact hs

#print axioms w0_leaf_136
theorem w0_leaf_137 : w0 137 = 0 := by
  have hpos : order.symm (77 : Fin 1024) = (137 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_77 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (137 : Fin 1024))]
  exact hs

#print axioms w0_leaf_137
theorem w0_leaf_138 : w0 138 = 0 := by
  have hpos : order.symm (92 : Fin 1024) = (138 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_92 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (138 : Fin 1024))]
  exact hs

#print axioms w0_leaf_138
theorem w0_leaf_139 : w0 139 = 0 := by
  have hpos : order.symm (93 : Fin 1024) = (139 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_93 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (139 : Fin 1024))]
  exact hs

#print axioms w0_leaf_139
theorem w0_leaf_140 : w0 140 = 0 := by
  have hpos : order.symm (108 : Fin 1024) = (140 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_108 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (140 : Fin 1024))]
  exact hs

#print axioms w0_leaf_140
theorem w0_leaf_141 : w0 141 = 0 := by
  have hpos : order.symm (109 : Fin 1024) = (141 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_109 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (141 : Fin 1024))]
  exact hs

#print axioms w0_leaf_141
theorem w0_leaf_142 : w0 142 = 0 := by
  have hpos : order.symm (124 : Fin 1024) = (142 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_124 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (142 : Fin 1024))]
  exact hs

#print axioms w0_leaf_142
theorem w0_leaf_143 : w0 143 = 0 := by
  have hpos : order.symm (125 : Fin 1024) = (143 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_125 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (143 : Fin 1024))]
  exact hs

#print axioms w0_leaf_143
theorem w0_leaf_144 : w0 144 = 0 := by
  have hpos : order.symm (140 : Fin 1024) = (144 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_140 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (144 : Fin 1024))]
  exact hs

#print axioms w0_leaf_144
theorem w0_leaf_145 : w0 145 = 0 := by
  have hpos : order.symm (141 : Fin 1024) = (145 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_141 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (145 : Fin 1024))]
  exact hs

#print axioms w0_leaf_145
theorem w0_leaf_146 : w0 146 = 0 := by
  have hpos : order.symm (156 : Fin 1024) = (146 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_156 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (146 : Fin 1024))]
  exact hs

#print axioms w0_leaf_146
theorem w0_leaf_147 : w0 147 = 0 := by
  have hpos : order.symm (157 : Fin 1024) = (147 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_157 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (147 : Fin 1024))]
  exact hs

#print axioms w0_leaf_147
theorem w0_leaf_148 : w0 148 = 0 := by
  have hpos : order.symm (172 : Fin 1024) = (148 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_172 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (148 : Fin 1024))]
  exact hs

#print axioms w0_leaf_148
theorem w0_leaf_149 : w0 149 = 0 := by
  have hpos : order.symm (173 : Fin 1024) = (149 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_173 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (149 : Fin 1024))]
  exact hs

#print axioms w0_leaf_149
theorem w0_leaf_150 : w0 150 = 0 := by
  have hpos : order.symm (188 : Fin 1024) = (150 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_188 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (150 : Fin 1024))]
  exact hs

#print axioms w0_leaf_150
theorem w0_leaf_151 : w0 151 = 0 := by
  have hpos : order.symm (189 : Fin 1024) = (151 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_189 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (151 : Fin 1024))]
  exact hs

#print axioms w0_leaf_151
theorem w0_leaf_152 : w0 152 = 0 := by
  have hpos : order.symm (204 : Fin 1024) = (152 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_204 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (152 : Fin 1024))]
  exact hs

#print axioms w0_leaf_152
theorem w0_leaf_153 : w0 153 = 0 := by
  have hpos : order.symm (205 : Fin 1024) = (153 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_205 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (153 : Fin 1024))]
  exact hs

#print axioms w0_leaf_153
theorem w0_leaf_154 : w0 154 = 0 := by
  have hpos : order.symm (220 : Fin 1024) = (154 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_220 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (154 : Fin 1024))]
  exact hs

#print axioms w0_leaf_154
theorem w0_leaf_155 : w0 155 = 0 := by
  have hpos : order.symm (221 : Fin 1024) = (155 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_221 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (155 : Fin 1024))]
  exact hs

#print axioms w0_leaf_155
theorem w0_leaf_156 : w0 156 = 0 := by
  have hpos : order.symm (236 : Fin 1024) = (156 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_236 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (156 : Fin 1024))]
  exact hs

#print axioms w0_leaf_156
theorem w0_leaf_157 : w0 157 = 0 := by
  have hpos : order.symm (237 : Fin 1024) = (157 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_237 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (157 : Fin 1024))]
  exact hs

#print axioms w0_leaf_157
theorem w0_leaf_158 : w0 158 = 0 := by
  have hpos : order.symm (252 : Fin 1024) = (158 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_252 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (158 : Fin 1024))]
  exact hs

#print axioms w0_leaf_158
theorem w0_leaf_159 : w0 159 = 0 := by
  have hpos : order.symm (253 : Fin 1024) = (159 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_253 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (159 : Fin 1024))]
  exact hs

#print axioms w0_leaf_159
theorem w0_leaf_160 : w0 160 = 0 := by
  have hpos : order.symm (268 : Fin 1024) = (160 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_268 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (160 : Fin 1024))]
  exact hs

#print axioms w0_leaf_160
theorem w0_leaf_161 : w0 161 = 0 := by
  have hpos : order.symm (269 : Fin 1024) = (161 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_269 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (161 : Fin 1024))]
  exact hs

#print axioms w0_leaf_161
theorem w0_leaf_162 : w0 162 = 0 := by
  have hpos : order.symm (284 : Fin 1024) = (162 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_284 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (162 : Fin 1024))]
  exact hs

#print axioms w0_leaf_162
theorem w0_leaf_163 : w0 163 = 0 := by
  have hpos : order.symm (285 : Fin 1024) = (163 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_285 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (163 : Fin 1024))]
  exact hs

#print axioms w0_leaf_163
theorem w0_leaf_164 : w0 164 = 0 := by
  have hpos : order.symm (300 : Fin 1024) = (164 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_300 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (164 : Fin 1024))]
  exact hs

#print axioms w0_leaf_164
theorem w0_leaf_165 : w0 165 = 0 := by
  have hpos : order.symm (301 : Fin 1024) = (165 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_301 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (165 : Fin 1024))]
  exact hs

#print axioms w0_leaf_165
theorem w0_leaf_166 : w0 166 = 0 := by
  have hpos : order.symm (316 : Fin 1024) = (166 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_316 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (166 : Fin 1024))]
  exact hs

#print axioms w0_leaf_166
theorem w0_leaf_167 : w0 167 = 0 := by
  have hpos : order.symm (317 : Fin 1024) = (167 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_317 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (167 : Fin 1024))]
  exact hs

#print axioms w0_leaf_167
theorem w0_leaf_168 : w0 168 = 0 := by
  have hpos : order.symm (332 : Fin 1024) = (168 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_332 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (168 : Fin 1024))]
  exact hs

#print axioms w0_leaf_168
theorem w0_leaf_169 : w0 169 = 0 := by
  have hpos : order.symm (333 : Fin 1024) = (169 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_333 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (169 : Fin 1024))]
  exact hs

#print axioms w0_leaf_169
theorem w0_leaf_170 : w0 170 = 0 := by
  have hpos : order.symm (348 : Fin 1024) = (170 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_348 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (170 : Fin 1024))]
  exact hs

#print axioms w0_leaf_170
theorem w0_leaf_171 : w0 171 = 0 := by
  have hpos : order.symm (349 : Fin 1024) = (171 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_349 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (171 : Fin 1024))]
  exact hs

#print axioms w0_leaf_171
theorem w0_leaf_172 : w0 172 = 0 := by
  have hpos : order.symm (364 : Fin 1024) = (172 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_364 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (172 : Fin 1024))]
  exact hs

#print axioms w0_leaf_172
theorem w0_leaf_173 : w0 173 = 0 := by
  have hpos : order.symm (365 : Fin 1024) = (173 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_365 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (173 : Fin 1024))]
  exact hs

#print axioms w0_leaf_173
theorem w0_leaf_174 : w0 174 = 0 := by
  have hpos : order.symm (380 : Fin 1024) = (174 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_380 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (174 : Fin 1024))]
  exact hs

#print axioms w0_leaf_174
theorem w0_leaf_175 : w0 175 = 0 := by
  have hpos : order.symm (381 : Fin 1024) = (175 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_381 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (175 : Fin 1024))]
  exact hs

#print axioms w0_leaf_175
theorem w0_leaf_176 : w0 176 = 0 := by
  have hpos : order.symm (396 : Fin 1024) = (176 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_396 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (176 : Fin 1024))]
  exact hs

#print axioms w0_leaf_176
theorem w0_leaf_177 : w0 177 = 0 := by
  have hpos : order.symm (397 : Fin 1024) = (177 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_397 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (177 : Fin 1024))]
  exact hs

#print axioms w0_leaf_177
theorem w0_leaf_178 : w0 178 = 0 := by
  have hpos : order.symm (412 : Fin 1024) = (178 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_412 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (178 : Fin 1024))]
  exact hs

#print axioms w0_leaf_178
theorem w0_leaf_179 : w0 179 = 0 := by
  have hpos : order.symm (413 : Fin 1024) = (179 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_413 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (179 : Fin 1024))]
  exact hs

#print axioms w0_leaf_179
theorem w0_leaf_180 : w0 180 = 0 := by
  have hpos : order.symm (428 : Fin 1024) = (180 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_428 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (180 : Fin 1024))]
  exact hs

#print axioms w0_leaf_180
theorem w0_leaf_181 : w0 181 = 0 := by
  have hpos : order.symm (429 : Fin 1024) = (181 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_429 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (181 : Fin 1024))]
  exact hs

#print axioms w0_leaf_181
theorem w0_leaf_182 : w0 182 = 0 := by
  have hpos : order.symm (444 : Fin 1024) = (182 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_444 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (182 : Fin 1024))]
  exact hs

#print axioms w0_leaf_182
theorem w0_leaf_183 : w0 183 = 0 := by
  have hpos : order.symm (445 : Fin 1024) = (183 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_445 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (183 : Fin 1024))]
  exact hs

#print axioms w0_leaf_183
theorem w0_leaf_184 : w0 184 = 0 := by
  have hpos : order.symm (460 : Fin 1024) = (184 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_460 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (184 : Fin 1024))]
  exact hs

#print axioms w0_leaf_184
theorem w0_leaf_185 : w0 185 = 0 := by
  have hpos : order.symm (461 : Fin 1024) = (185 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_461 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (185 : Fin 1024))]
  exact hs

#print axioms w0_leaf_185
theorem w0_leaf_186 : w0 186 = 0 := by
  have hpos : order.symm (476 : Fin 1024) = (186 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_476 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (186 : Fin 1024))]
  exact hs

#print axioms w0_leaf_186
theorem w0_leaf_187 : w0 187 = 0 := by
  have hpos : order.symm (477 : Fin 1024) = (187 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_477 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (187 : Fin 1024))]
  exact hs

#print axioms w0_leaf_187
theorem w0_leaf_188 : w0 188 = 0 := by
  have hpos : order.symm (492 : Fin 1024) = (188 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_492 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (188 : Fin 1024))]
  exact hs

#print axioms w0_leaf_188
theorem w0_leaf_189 : w0 189 = 0 := by
  have hpos : order.symm (493 : Fin 1024) = (189 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_493 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (189 : Fin 1024))]
  exact hs

#print axioms w0_leaf_189
theorem w0_leaf_190 : w0 190 = 0 := by
  have hpos : order.symm (508 : Fin 1024) = (190 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_508 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (190 : Fin 1024))]
  exact hs

#print axioms w0_leaf_190
theorem w0_leaf_191 : w0 191 = 0 := by
  have hpos : order.symm (509 : Fin 1024) = (191 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_509 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (191 : Fin 1024))]
  exact hs

#print axioms w0_leaf_191
theorem w0_leaf_192 : w0 192 = 0 := by
  have hpos : order.symm (524 : Fin 1024) = (192 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_524 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (192 : Fin 1024))]
  exact hs

#print axioms w0_leaf_192
theorem w0_leaf_193 : w0 193 = 0 := by
  have hpos : order.symm (525 : Fin 1024) = (193 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_525 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (193 : Fin 1024))]
  exact hs

#print axioms w0_leaf_193
theorem w0_leaf_194 : w0 194 = 0 := by
  have hpos : order.symm (540 : Fin 1024) = (194 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_540 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (194 : Fin 1024))]
  exact hs

#print axioms w0_leaf_194
theorem w0_leaf_195 : w0 195 = 0 := by
  have hpos : order.symm (541 : Fin 1024) = (195 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_541 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (195 : Fin 1024))]
  exact hs

#print axioms w0_leaf_195
theorem w0_leaf_196 : w0 196 = 0 := by
  have hpos : order.symm (556 : Fin 1024) = (196 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_556 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (196 : Fin 1024))]
  exact hs

#print axioms w0_leaf_196
theorem w0_leaf_197 : w0 197 = 0 := by
  have hpos : order.symm (557 : Fin 1024) = (197 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_557 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (197 : Fin 1024))]
  exact hs

#print axioms w0_leaf_197
theorem w0_leaf_198 : w0 198 = 0 := by
  have hpos : order.symm (572 : Fin 1024) = (198 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_572 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (198 : Fin 1024))]
  exact hs

#print axioms w0_leaf_198
theorem w0_leaf_199 : w0 199 = 0 := by
  have hpos : order.symm (573 : Fin 1024) = (199 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_573 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (199 : Fin 1024))]
  exact hs

#print axioms w0_leaf_199
theorem w0_leaf_200 : w0 200 = 0 := by
  have hpos : order.symm (588 : Fin 1024) = (200 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_588 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (200 : Fin 1024))]
  exact hs

#print axioms w0_leaf_200
theorem w0_leaf_201 : w0 201 = 0 := by
  have hpos : order.symm (589 : Fin 1024) = (201 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_589 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (201 : Fin 1024))]
  exact hs

#print axioms w0_leaf_201
theorem w0_leaf_202 : w0 202 = 0 := by
  have hpos : order.symm (604 : Fin 1024) = (202 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_604 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (202 : Fin 1024))]
  exact hs

#print axioms w0_leaf_202
theorem w0_leaf_203 : w0 203 = 0 := by
  have hpos : order.symm (605 : Fin 1024) = (203 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_605 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (203 : Fin 1024))]
  exact hs

#print axioms w0_leaf_203
theorem w0_leaf_204 : w0 204 = 0 := by
  have hpos : order.symm (620 : Fin 1024) = (204 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_620 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (204 : Fin 1024))]
  exact hs

#print axioms w0_leaf_204
theorem w0_leaf_205 : w0 205 = 0 := by
  have hpos : order.symm (621 : Fin 1024) = (205 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_621 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (205 : Fin 1024))]
  exact hs

#print axioms w0_leaf_205
theorem w0_leaf_206 : w0 206 = 0 := by
  have hpos : order.symm (636 : Fin 1024) = (206 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_636 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (206 : Fin 1024))]
  exact hs

#print axioms w0_leaf_206
theorem w0_leaf_207 : w0 207 = 0 := by
  have hpos : order.symm (637 : Fin 1024) = (207 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_637 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (207 : Fin 1024))]
  exact hs

#print axioms w0_leaf_207
theorem w0_leaf_208 : w0 208 = 0 := by
  have hpos : order.symm (652 : Fin 1024) = (208 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_652 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (208 : Fin 1024))]
  exact hs

#print axioms w0_leaf_208
theorem w0_leaf_209 : w0 209 = 0 := by
  have hpos : order.symm (653 : Fin 1024) = (209 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_653 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (209 : Fin 1024))]
  exact hs

#print axioms w0_leaf_209
theorem w0_leaf_210 : w0 210 = 0 := by
  have hpos : order.symm (668 : Fin 1024) = (210 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_668 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (210 : Fin 1024))]
  exact hs

#print axioms w0_leaf_210
theorem w0_leaf_211 : w0 211 = 0 := by
  have hpos : order.symm (669 : Fin 1024) = (211 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_669 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (211 : Fin 1024))]
  exact hs

#print axioms w0_leaf_211
theorem w0_leaf_212 : w0 212 = 0 := by
  have hpos : order.symm (684 : Fin 1024) = (212 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_684 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (212 : Fin 1024))]
  exact hs

#print axioms w0_leaf_212
theorem w0_leaf_213 : w0 213 = 0 := by
  have hpos : order.symm (685 : Fin 1024) = (213 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_685 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (213 : Fin 1024))]
  exact hs

#print axioms w0_leaf_213
theorem w0_leaf_214 : w0 214 = 0 := by
  have hpos : order.symm (700 : Fin 1024) = (214 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_700 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (214 : Fin 1024))]
  exact hs

#print axioms w0_leaf_214
theorem w0_leaf_215 : w0 215 = 0 := by
  have hpos : order.symm (701 : Fin 1024) = (215 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_701 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (215 : Fin 1024))]
  exact hs

#print axioms w0_leaf_215
theorem w0_leaf_216 : w0 216 = 0 := by
  have hpos : order.symm (716 : Fin 1024) = (216 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_716 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (216 : Fin 1024))]
  exact hs

#print axioms w0_leaf_216
theorem w0_leaf_217 : w0 217 = 0 := by
  have hpos : order.symm (717 : Fin 1024) = (217 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_717 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (217 : Fin 1024))]
  exact hs

#print axioms w0_leaf_217
theorem w0_leaf_218 : w0 218 = 0 := by
  have hpos : order.symm (732 : Fin 1024) = (218 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_732 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (218 : Fin 1024))]
  exact hs

#print axioms w0_leaf_218
theorem w0_leaf_219 : w0 219 = 0 := by
  have hpos : order.symm (733 : Fin 1024) = (219 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_733 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (219 : Fin 1024))]
  exact hs

#print axioms w0_leaf_219
theorem w0_leaf_220 : w0 220 = 0 := by
  have hpos : order.symm (748 : Fin 1024) = (220 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_748 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (220 : Fin 1024))]
  exact hs

#print axioms w0_leaf_220
theorem w0_leaf_221 : w0 221 = 0 := by
  have hpos : order.symm (749 : Fin 1024) = (221 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_749 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (221 : Fin 1024))]
  exact hs

#print axioms w0_leaf_221
theorem w0_leaf_222 : w0 222 = 0 := by
  have hpos : order.symm (764 : Fin 1024) = (222 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_764 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (222 : Fin 1024))]
  exact hs

#print axioms w0_leaf_222
theorem w0_leaf_223 : w0 223 = 0 := by
  have hpos : order.symm (765 : Fin 1024) = (223 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_765 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (223 : Fin 1024))]
  exact hs

#print axioms w0_leaf_223
theorem w0_leaf_224 : w0 224 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (780 : Fin 1024) = (224 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeaves.point0_candidate780_transport_exact (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (224 : Fin 1024))]
  exact hs

#print axioms w0_leaf_224
theorem w0_leaf_225 : w0 225 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (781 : Fin 1024) = (225 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_781 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (225 : Fin 1024))]
  exact hs

#print axioms w0_leaf_225
theorem w0_leaf_226 : w0 226 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (796 : Fin 1024) = (226 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_796 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (226 : Fin 1024))]
  exact hs

#print axioms w0_leaf_226
theorem w0_leaf_227 : w0 227 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (797 : Fin 1024) = (227 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_797 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (227 : Fin 1024))]
  exact hs

#print axioms w0_leaf_227
theorem w0_leaf_228 : w0 228 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (812 : Fin 1024) = (228 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_812 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (228 : Fin 1024))]
  exact hs

#print axioms w0_leaf_228
theorem w0_leaf_229 : w0 229 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (813 : Fin 1024) = (229 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_813 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (229 : Fin 1024))]
  exact hs

#print axioms w0_leaf_229
theorem w0_leaf_230 : w0 230 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (828 : Fin 1024) = (230 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_828 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (230 : Fin 1024))]
  exact hs

#print axioms w0_leaf_230
theorem w0_leaf_231 : w0 231 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (829 : Fin 1024) = (231 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_829 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (231 : Fin 1024))]
  exact hs

#print axioms w0_leaf_231
theorem w0_leaf_232 : w0 232 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (844 : Fin 1024) = (232 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_844 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (232 : Fin 1024))]
  exact hs

#print axioms w0_leaf_232
theorem w0_leaf_233 : w0 233 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (845 : Fin 1024) = (233 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_845 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (233 : Fin 1024))]
  exact hs

#print axioms w0_leaf_233
theorem w0_leaf_234 : w0 234 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (860 : Fin 1024) = (234 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_860 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (234 : Fin 1024))]
  exact hs

#print axioms w0_leaf_234
theorem w0_leaf_235 : w0 235 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (861 : Fin 1024) = (235 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_861 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (235 : Fin 1024))]
  exact hs

#print axioms w0_leaf_235
theorem w0_leaf_236 : w0 236 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (876 : Fin 1024) = (236 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_876 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (236 : Fin 1024))]
  exact hs

#print axioms w0_leaf_236
theorem w0_leaf_237 : w0 237 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (877 : Fin 1024) = (237 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_877 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (237 : Fin 1024))]
  exact hs

#print axioms w0_leaf_237
theorem w0_leaf_238 : w0 238 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (892 : Fin 1024) = (238 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_892 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (238 : Fin 1024))]
  exact hs

#print axioms w0_leaf_238
theorem w0_leaf_239 : w0 239 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (893 : Fin 1024) = (239 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_893 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (239 : Fin 1024))]
  exact hs

#print axioms w0_leaf_239
theorem w0_leaf_240 : w0 240 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (908 : Fin 1024) = (240 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_908 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (240 : Fin 1024))]
  exact hs

#print axioms w0_leaf_240
theorem w0_leaf_241 : w0 241 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (909 : Fin 1024) = (241 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_909 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (241 : Fin 1024))]
  exact hs

#print axioms w0_leaf_241
theorem w0_leaf_242 : w0 242 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (924 : Fin 1024) = (242 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_924 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (242 : Fin 1024))]
  exact hs

#print axioms w0_leaf_242
theorem w0_leaf_243 : w0 243 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (925 : Fin 1024) = (243 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_925 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (243 : Fin 1024))]
  exact hs

#print axioms w0_leaf_243
theorem w0_leaf_244 : w0 244 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (940 : Fin 1024) = (244 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_940 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (244 : Fin 1024))]
  exact hs

#print axioms w0_leaf_244
theorem w0_leaf_245 : w0 245 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (941 : Fin 1024) = (245 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_941 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (245 : Fin 1024))]
  exact hs

#print axioms w0_leaf_245
theorem w0_leaf_246 : w0 246 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (956 : Fin 1024) = (246 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_956 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (246 : Fin 1024))]
  exact hs

#print axioms w0_leaf_246
theorem w0_leaf_247 : w0 247 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (957 : Fin 1024) = (247 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_957 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (247 : Fin 1024))]
  exact hs

#print axioms w0_leaf_247
theorem w0_leaf_248 : w0 248 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (972 : Fin 1024) = (248 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_972 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (248 : Fin 1024))]
  exact hs

#print axioms w0_leaf_248
theorem w0_leaf_249 : w0 249 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (973 : Fin 1024) = (249 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_973 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (249 : Fin 1024))]
  exact hs

#print axioms w0_leaf_249
theorem w0_leaf_250 : w0 250 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (988 : Fin 1024) = (250 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_988 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (250 : Fin 1024))]
  exact hs

#print axioms w0_leaf_250
theorem w0_leaf_251 : w0 251 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (989 : Fin 1024) = (251 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_989 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (251 : Fin 1024))]
  exact hs

#print axioms w0_leaf_251
theorem w0_leaf_252 : w0 252 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (1004 : Fin 1024) = (252 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_1004 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (252 : Fin 1024))]
  exact hs

#print axioms w0_leaf_252
theorem w0_leaf_253 : w0 253 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (1005 : Fin 1024) = (253 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1005 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (253 : Fin 1024))]
  exact hs

#print axioms w0_leaf_253
theorem w0_leaf_254 : w0 254 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (1020 : Fin 1024) = (254 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_1020 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (254 : Fin 1024))]
  exact hs

#print axioms w0_leaf_254
theorem w0_leaf_255 : w0 255 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (1021 : Fin 1024) = (255 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_1021 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (255 : Fin 1024))]
  exact hs

#print axioms w0_leaf_255
theorem w0_leaf_256 : w0 256 = 0 := by
  have hpos : order.symm (10 : Fin 1024) = (256 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_10 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (256 : Fin 1024))]
  exact hs

#print axioms w0_leaf_256
theorem w0_leaf_257 : w0 257 = 0 := by
  have hpos : order.symm (11 : Fin 1024) = (257 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_11 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (257 : Fin 1024))]
  exact hs

#print axioms w0_leaf_257
theorem w0_leaf_258 : w0 258 = 0 := by
  have hpos : order.symm (26 : Fin 1024) = (258 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_26 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (258 : Fin 1024))]
  exact hs

#print axioms w0_leaf_258
theorem w0_leaf_259 : w0 259 = 0 := by
  have hpos : order.symm (27 : Fin 1024) = (259 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_27 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (259 : Fin 1024))]
  exact hs

#print axioms w0_leaf_259
theorem w0_leaf_260 : w0 260 = 0 := by
  have hpos : order.symm (42 : Fin 1024) = (260 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_42 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (260 : Fin 1024))]
  exact hs

#print axioms w0_leaf_260
theorem w0_leaf_261 : w0 261 = 0 := by
  have hpos : order.symm (43 : Fin 1024) = (261 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_43 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (261 : Fin 1024))]
  exact hs

#print axioms w0_leaf_261
theorem w0_leaf_262 : w0 262 = 0 := by
  have hpos : order.symm (58 : Fin 1024) = (262 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_58 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (262 : Fin 1024))]
  exact hs

#print axioms w0_leaf_262
theorem w0_leaf_263 : w0 263 = 0 := by
  have hpos : order.symm (59 : Fin 1024) = (263 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_59 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (263 : Fin 1024))]
  exact hs

#print axioms w0_leaf_263
theorem w0_leaf_264 : w0 264 = 0 := by
  have hpos : order.symm (74 : Fin 1024) = (264 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_74 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (264 : Fin 1024))]
  exact hs

#print axioms w0_leaf_264
theorem w0_leaf_265 : w0 265 = 0 := by
  have hpos : order.symm (75 : Fin 1024) = (265 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_75 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (265 : Fin 1024))]
  exact hs

#print axioms w0_leaf_265
theorem w0_leaf_266 : w0 266 = 0 := by
  have hpos : order.symm (90 : Fin 1024) = (266 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_90 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (266 : Fin 1024))]
  exact hs

#print axioms w0_leaf_266
theorem w0_leaf_267 : w0 267 = 0 := by
  have hpos : order.symm (91 : Fin 1024) = (267 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_91 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (267 : Fin 1024))]
  exact hs

#print axioms w0_leaf_267
theorem w0_leaf_268 : w0 268 = 0 := by
  have hpos : order.symm (106 : Fin 1024) = (268 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_106 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (268 : Fin 1024))]
  exact hs

#print axioms w0_leaf_268
theorem w0_leaf_269 : w0 269 = 0 := by
  have hpos : order.symm (107 : Fin 1024) = (269 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_107 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (269 : Fin 1024))]
  exact hs

#print axioms w0_leaf_269
theorem w0_leaf_270 : w0 270 = 0 := by
  have hpos : order.symm (122 : Fin 1024) = (270 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_122 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (270 : Fin 1024))]
  exact hs

#print axioms w0_leaf_270
theorem w0_leaf_271 : w0 271 = 0 := by
  have hpos : order.symm (123 : Fin 1024) = (271 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_123 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (271 : Fin 1024))]
  exact hs

#print axioms w0_leaf_271
theorem w0_leaf_272 : w0 272 = 0 := by
  have hpos : order.symm (138 : Fin 1024) = (272 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_138 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (272 : Fin 1024))]
  exact hs

#print axioms w0_leaf_272
theorem w0_leaf_273 : w0 273 = 0 := by
  have hpos : order.symm (139 : Fin 1024) = (273 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_139 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (273 : Fin 1024))]
  exact hs

#print axioms w0_leaf_273
theorem w0_leaf_274 : w0 274 = 0 := by
  have hpos : order.symm (154 : Fin 1024) = (274 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_154 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (274 : Fin 1024))]
  exact hs

#print axioms w0_leaf_274
theorem w0_leaf_275 : w0 275 = 0 := by
  have hpos : order.symm (155 : Fin 1024) = (275 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_155 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (275 : Fin 1024))]
  exact hs

#print axioms w0_leaf_275
theorem w0_leaf_276 : w0 276 = 0 := by
  have hpos : order.symm (170 : Fin 1024) = (276 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_170 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (276 : Fin 1024))]
  exact hs

#print axioms w0_leaf_276
theorem w0_leaf_277 : w0 277 = 0 := by
  have hpos : order.symm (171 : Fin 1024) = (277 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_171 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (277 : Fin 1024))]
  exact hs

#print axioms w0_leaf_277
theorem w0_leaf_278 : w0 278 = 0 := by
  have hpos : order.symm (186 : Fin 1024) = (278 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_186 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (278 : Fin 1024))]
  exact hs

#print axioms w0_leaf_278
theorem w0_leaf_279 : w0 279 = 0 := by
  have hpos : order.symm (187 : Fin 1024) = (279 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_187 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (279 : Fin 1024))]
  exact hs

#print axioms w0_leaf_279
theorem w0_leaf_280 : w0 280 = 0 := by
  have hpos : order.symm (202 : Fin 1024) = (280 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_202 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (280 : Fin 1024))]
  exact hs

#print axioms w0_leaf_280
theorem w0_leaf_281 : w0 281 = 0 := by
  have hpos : order.symm (203 : Fin 1024) = (281 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_203 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (281 : Fin 1024))]
  exact hs

#print axioms w0_leaf_281
theorem w0_leaf_282 : w0 282 = 0 := by
  have hpos : order.symm (218 : Fin 1024) = (282 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_218 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (282 : Fin 1024))]
  exact hs

#print axioms w0_leaf_282
theorem w0_leaf_283 : w0 283 = 0 := by
  have hpos : order.symm (219 : Fin 1024) = (283 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_219 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (283 : Fin 1024))]
  exact hs

#print axioms w0_leaf_283
theorem w0_leaf_284 : w0 284 = 0 := by
  have hpos : order.symm (234 : Fin 1024) = (284 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_234 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (284 : Fin 1024))]
  exact hs

#print axioms w0_leaf_284
theorem w0_leaf_285 : w0 285 = 0 := by
  have hpos : order.symm (235 : Fin 1024) = (285 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_235 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (285 : Fin 1024))]
  exact hs

#print axioms w0_leaf_285
theorem w0_leaf_286 : w0 286 = 0 := by
  have hpos : order.symm (250 : Fin 1024) = (286 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_250 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (286 : Fin 1024))]
  exact hs

#print axioms w0_leaf_286
theorem w0_leaf_287 : w0 287 = 0 := by
  have hpos : order.symm (251 : Fin 1024) = (287 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_251 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (287 : Fin 1024))]
  exact hs

#print axioms w0_leaf_287
theorem w0_leaf_288 : w0 288 = 0 := by
  have hpos : order.symm (266 : Fin 1024) = (288 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_266 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (288 : Fin 1024))]
  exact hs

#print axioms w0_leaf_288
theorem w0_leaf_289 : w0 289 = 0 := by
  have hpos : order.symm (267 : Fin 1024) = (289 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_267 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (289 : Fin 1024))]
  exact hs

#print axioms w0_leaf_289
theorem w0_leaf_290 : w0 290 = 0 := by
  have hpos : order.symm (282 : Fin 1024) = (290 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_282 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (290 : Fin 1024))]
  exact hs

#print axioms w0_leaf_290
theorem w0_leaf_291 : w0 291 = 0 := by
  have hpos : order.symm (283 : Fin 1024) = (291 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_283 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (291 : Fin 1024))]
  exact hs

#print axioms w0_leaf_291
theorem w0_leaf_292 : w0 292 = 0 := by
  have hpos : order.symm (298 : Fin 1024) = (292 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_298 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (292 : Fin 1024))]
  exact hs

#print axioms w0_leaf_292
theorem w0_leaf_293 : w0 293 = 0 := by
  have hpos : order.symm (299 : Fin 1024) = (293 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_299 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (293 : Fin 1024))]
  exact hs

#print axioms w0_leaf_293
theorem w0_leaf_294 : w0 294 = 0 := by
  have hpos : order.symm (314 : Fin 1024) = (294 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_314 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (294 : Fin 1024))]
  exact hs

#print axioms w0_leaf_294
theorem w0_leaf_295 : w0 295 = 0 := by
  have hpos : order.symm (315 : Fin 1024) = (295 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_315 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (295 : Fin 1024))]
  exact hs

#print axioms w0_leaf_295
theorem w0_leaf_296 : w0 296 = 0 := by
  have hpos : order.symm (330 : Fin 1024) = (296 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_330 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (296 : Fin 1024))]
  exact hs

#print axioms w0_leaf_296
theorem w0_leaf_297 : w0 297 = 0 := by
  have hpos : order.symm (331 : Fin 1024) = (297 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_331 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (297 : Fin 1024))]
  exact hs

#print axioms w0_leaf_297
theorem w0_leaf_298 : w0 298 = 0 := by
  have hpos : order.symm (346 : Fin 1024) = (298 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_346 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (298 : Fin 1024))]
  exact hs

#print axioms w0_leaf_298
theorem w0_leaf_299 : w0 299 = 0 := by
  have hpos : order.symm (347 : Fin 1024) = (299 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_347 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (299 : Fin 1024))]
  exact hs

#print axioms w0_leaf_299
theorem w0_leaf_300 : w0 300 = 0 := by
  have hpos : order.symm (362 : Fin 1024) = (300 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_362 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (300 : Fin 1024))]
  exact hs

#print axioms w0_leaf_300
theorem w0_leaf_301 : w0 301 = 0 := by
  have hpos : order.symm (363 : Fin 1024) = (301 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_363 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (301 : Fin 1024))]
  exact hs

#print axioms w0_leaf_301
theorem w0_leaf_302 : w0 302 = 0 := by
  have hpos : order.symm (378 : Fin 1024) = (302 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_378 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (302 : Fin 1024))]
  exact hs

#print axioms w0_leaf_302
theorem w0_leaf_303 : w0 303 = 0 := by
  have hpos : order.symm (379 : Fin 1024) = (303 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_379 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (303 : Fin 1024))]
  exact hs

#print axioms w0_leaf_303
theorem w0_leaf_304 : w0 304 = 0 := by
  have hpos : order.symm (394 : Fin 1024) = (304 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_394 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (304 : Fin 1024))]
  exact hs

#print axioms w0_leaf_304
theorem w0_leaf_305 : w0 305 = 0 := by
  have hpos : order.symm (395 : Fin 1024) = (305 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_395 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (305 : Fin 1024))]
  exact hs

#print axioms w0_leaf_305
theorem w0_leaf_306 : w0 306 = 0 := by
  have hpos : order.symm (410 : Fin 1024) = (306 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_410 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (306 : Fin 1024))]
  exact hs

#print axioms w0_leaf_306
theorem w0_leaf_307 : w0 307 = 0 := by
  have hpos : order.symm (411 : Fin 1024) = (307 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_411 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (307 : Fin 1024))]
  exact hs

#print axioms w0_leaf_307
theorem w0_leaf_308 : w0 308 = 0 := by
  have hpos : order.symm (426 : Fin 1024) = (308 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_426 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (308 : Fin 1024))]
  exact hs

#print axioms w0_leaf_308
theorem w0_leaf_309 : w0 309 = 0 := by
  have hpos : order.symm (427 : Fin 1024) = (309 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_427 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (309 : Fin 1024))]
  exact hs

#print axioms w0_leaf_309
theorem w0_leaf_310 : w0 310 = 0 := by
  have hpos : order.symm (442 : Fin 1024) = (310 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_442 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (310 : Fin 1024))]
  exact hs

#print axioms w0_leaf_310
theorem w0_leaf_311 : w0 311 = 0 := by
  have hpos : order.symm (443 : Fin 1024) = (311 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_443 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (311 : Fin 1024))]
  exact hs

#print axioms w0_leaf_311
theorem w0_leaf_312 : w0 312 = 0 := by
  have hpos : order.symm (458 : Fin 1024) = (312 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_458 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (312 : Fin 1024))]
  exact hs

#print axioms w0_leaf_312
theorem w0_leaf_313 : w0 313 = 0 := by
  have hpos : order.symm (459 : Fin 1024) = (313 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_459 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (313 : Fin 1024))]
  exact hs

#print axioms w0_leaf_313
theorem w0_leaf_314 : w0 314 = 0 := by
  have hpos : order.symm (474 : Fin 1024) = (314 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_474 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (314 : Fin 1024))]
  exact hs

#print axioms w0_leaf_314
theorem w0_leaf_315 : w0 315 = 0 := by
  have hpos : order.symm (475 : Fin 1024) = (315 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_475 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (315 : Fin 1024))]
  exact hs

#print axioms w0_leaf_315
theorem w0_leaf_316 : w0 316 = 0 := by
  have hpos : order.symm (490 : Fin 1024) = (316 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_490 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (316 : Fin 1024))]
  exact hs

#print axioms w0_leaf_316
theorem w0_leaf_317 : w0 317 = 0 := by
  have hpos : order.symm (491 : Fin 1024) = (317 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_491 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (317 : Fin 1024))]
  exact hs

#print axioms w0_leaf_317
theorem w0_leaf_318 : w0 318 = 0 := by
  have hpos : order.symm (506 : Fin 1024) = (318 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_506 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (318 : Fin 1024))]
  exact hs

#print axioms w0_leaf_318
theorem w0_leaf_319 : w0 319 = 0 := by
  have hpos : order.symm (507 : Fin 1024) = (319 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_507 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (319 : Fin 1024))]
  exact hs

#print axioms w0_leaf_319
theorem w0_leaf_320 : w0 320 = 0 := by
  have hpos : order.symm (522 : Fin 1024) = (320 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_522 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (320 : Fin 1024))]
  exact hs

#print axioms w0_leaf_320
theorem w0_leaf_321 : w0 321 = 0 := by
  have hpos : order.symm (523 : Fin 1024) = (321 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_523 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (321 : Fin 1024))]
  exact hs

#print axioms w0_leaf_321
theorem w0_leaf_322 : w0 322 = 0 := by
  have hpos : order.symm (538 : Fin 1024) = (322 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_538 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (322 : Fin 1024))]
  exact hs

#print axioms w0_leaf_322
theorem w0_leaf_323 : w0 323 = 0 := by
  have hpos : order.symm (539 : Fin 1024) = (323 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_539 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (323 : Fin 1024))]
  exact hs

#print axioms w0_leaf_323
theorem w0_leaf_324 : w0 324 = 0 := by
  have hpos : order.symm (554 : Fin 1024) = (324 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_554 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (324 : Fin 1024))]
  exact hs

#print axioms w0_leaf_324
theorem w0_leaf_325 : w0 325 = 0 := by
  have hpos : order.symm (555 : Fin 1024) = (325 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_555 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (325 : Fin 1024))]
  exact hs

#print axioms w0_leaf_325
theorem w0_leaf_326 : w0 326 = 0 := by
  have hpos : order.symm (570 : Fin 1024) = (326 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_570 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (326 : Fin 1024))]
  exact hs

#print axioms w0_leaf_326
theorem w0_leaf_327 : w0 327 = 0 := by
  have hpos : order.symm (571 : Fin 1024) = (327 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_571 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (327 : Fin 1024))]
  exact hs

#print axioms w0_leaf_327
theorem w0_leaf_328 : w0 328 = 0 := by
  have hpos : order.symm (586 : Fin 1024) = (328 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_586 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (328 : Fin 1024))]
  exact hs

#print axioms w0_leaf_328
theorem w0_leaf_329 : w0 329 = 0 := by
  have hpos : order.symm (587 : Fin 1024) = (329 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_587 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (329 : Fin 1024))]
  exact hs

#print axioms w0_leaf_329
theorem w0_leaf_330 : w0 330 = 0 := by
  have hpos : order.symm (602 : Fin 1024) = (330 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_602 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (330 : Fin 1024))]
  exact hs

#print axioms w0_leaf_330
theorem w0_leaf_331 : w0 331 = 0 := by
  have hpos : order.symm (603 : Fin 1024) = (331 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_603 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (331 : Fin 1024))]
  exact hs

#print axioms w0_leaf_331
theorem w0_leaf_332 : w0 332 = 0 := by
  have hpos : order.symm (618 : Fin 1024) = (332 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_618 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (332 : Fin 1024))]
  exact hs

#print axioms w0_leaf_332
theorem w0_leaf_333 : w0 333 = 0 := by
  have hpos : order.symm (619 : Fin 1024) = (333 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_619 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (333 : Fin 1024))]
  exact hs

#print axioms w0_leaf_333
theorem w0_leaf_334 : w0 334 = 0 := by
  have hpos : order.symm (634 : Fin 1024) = (334 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_634 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (334 : Fin 1024))]
  exact hs

#print axioms w0_leaf_334
theorem w0_leaf_335 : w0 335 = 0 := by
  have hpos : order.symm (635 : Fin 1024) = (335 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_635 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (335 : Fin 1024))]
  exact hs

#print axioms w0_leaf_335
theorem w0_leaf_336 : w0 336 = 0 := by
  have hpos : order.symm (650 : Fin 1024) = (336 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_650 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (336 : Fin 1024))]
  exact hs

#print axioms w0_leaf_336
theorem w0_leaf_337 : w0 337 = 0 := by
  have hpos : order.symm (651 : Fin 1024) = (337 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_651 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (337 : Fin 1024))]
  exact hs

#print axioms w0_leaf_337
theorem w0_leaf_338 : w0 338 = 0 := by
  have hpos : order.symm (666 : Fin 1024) = (338 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_666 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (338 : Fin 1024))]
  exact hs

#print axioms w0_leaf_338
theorem w0_leaf_339 : w0 339 = 0 := by
  have hpos : order.symm (667 : Fin 1024) = (339 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_667 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (339 : Fin 1024))]
  exact hs

#print axioms w0_leaf_339
theorem w0_leaf_340 : w0 340 = 0 := by
  have hpos : order.symm (682 : Fin 1024) = (340 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_682 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (340 : Fin 1024))]
  exact hs

#print axioms w0_leaf_340
theorem w0_leaf_341 : w0 341 = 0 := by
  have hpos : order.symm (683 : Fin 1024) = (341 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_683 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (341 : Fin 1024))]
  exact hs

#print axioms w0_leaf_341
theorem w0_leaf_342 : w0 342 = 0 := by
  have hpos : order.symm (698 : Fin 1024) = (342 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_698 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (342 : Fin 1024))]
  exact hs

#print axioms w0_leaf_342
theorem w0_leaf_343 : w0 343 = 0 := by
  have hpos : order.symm (699 : Fin 1024) = (343 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_699 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (343 : Fin 1024))]
  exact hs

#print axioms w0_leaf_343
theorem w0_leaf_344 : w0 344 = 0 := by
  have hpos : order.symm (714 : Fin 1024) = (344 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_714 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (344 : Fin 1024))]
  exact hs

#print axioms w0_leaf_344
theorem w0_leaf_345 : w0 345 = 0 := by
  have hpos : order.symm (715 : Fin 1024) = (345 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_715 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (345 : Fin 1024))]
  exact hs

#print axioms w0_leaf_345
theorem w0_leaf_346 : w0 346 = 0 := by
  have hpos : order.symm (730 : Fin 1024) = (346 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_730 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (346 : Fin 1024))]
  exact hs

#print axioms w0_leaf_346
theorem w0_leaf_347 : w0 347 = 0 := by
  have hpos : order.symm (731 : Fin 1024) = (347 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_731 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (347 : Fin 1024))]
  exact hs

#print axioms w0_leaf_347
theorem w0_leaf_348 : w0 348 = 0 := by
  have hpos : order.symm (746 : Fin 1024) = (348 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_746 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (348 : Fin 1024))]
  exact hs

#print axioms w0_leaf_348
theorem w0_leaf_349 : w0 349 = 0 := by
  have hpos : order.symm (747 : Fin 1024) = (349 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_747 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (349 : Fin 1024))]
  exact hs

#print axioms w0_leaf_349
theorem w0_leaf_350 : w0 350 = 0 := by
  have hpos : order.symm (762 : Fin 1024) = (350 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_762 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (350 : Fin 1024))]
  exact hs

#print axioms w0_leaf_350
theorem w0_leaf_351 : w0 351 = 0 := by
  have hpos : order.symm (763 : Fin 1024) = (351 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_763 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (351 : Fin 1024))]
  exact hs

#print axioms w0_leaf_351
theorem w0_leaf_352 : w0 352 = 0 := by
  have hpos : order.symm (778 : Fin 1024) = (352 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_778 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (352 : Fin 1024))]
  exact hs

#print axioms w0_leaf_352
theorem w0_leaf_353 : w0 353 = 0 := by
  have hpos : order.symm (779 : Fin 1024) = (353 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_779 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (353 : Fin 1024))]
  exact hs

#print axioms w0_leaf_353
theorem w0_leaf_354 : w0 354 = 0 := by
  have hpos : order.symm (794 : Fin 1024) = (354 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_794 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (354 : Fin 1024))]
  exact hs

#print axioms w0_leaf_354
theorem w0_leaf_355 : w0 355 = 0 := by
  have hpos : order.symm (795 : Fin 1024) = (355 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_795 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (355 : Fin 1024))]
  exact hs

#print axioms w0_leaf_355
theorem w0_leaf_356 : w0 356 = 0 := by
  have hpos : order.symm (810 : Fin 1024) = (356 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_810 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (356 : Fin 1024))]
  exact hs

#print axioms w0_leaf_356
theorem w0_leaf_357 : w0 357 = 0 := by
  have hpos : order.symm (811 : Fin 1024) = (357 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_811 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (357 : Fin 1024))]
  exact hs

#print axioms w0_leaf_357
theorem w0_leaf_358 : w0 358 = 0 := by
  have hpos : order.symm (826 : Fin 1024) = (358 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_826 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (358 : Fin 1024))]
  exact hs

#print axioms w0_leaf_358
theorem w0_leaf_359 : w0 359 = 0 := by
  have hpos : order.symm (827 : Fin 1024) = (359 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_827 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (359 : Fin 1024))]
  exact hs

#print axioms w0_leaf_359
theorem w0_leaf_360 : w0 360 = 0 := by
  have hpos : order.symm (842 : Fin 1024) = (360 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_842 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (360 : Fin 1024))]
  exact hs

#print axioms w0_leaf_360
theorem w0_leaf_361 : w0 361 = 0 := by
  have hpos : order.symm (843 : Fin 1024) = (361 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_843 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (361 : Fin 1024))]
  exact hs

#print axioms w0_leaf_361
theorem w0_leaf_362 : w0 362 = 0 := by
  have hpos : order.symm (858 : Fin 1024) = (362 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_858 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (362 : Fin 1024))]
  exact hs

#print axioms w0_leaf_362
theorem w0_leaf_363 : w0 363 = 0 := by
  have hpos : order.symm (859 : Fin 1024) = (363 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_859 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (363 : Fin 1024))]
  exact hs

#print axioms w0_leaf_363
theorem w0_leaf_364 : w0 364 = 0 := by
  have hpos : order.symm (874 : Fin 1024) = (364 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_874 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (364 : Fin 1024))]
  exact hs

#print axioms w0_leaf_364
theorem w0_leaf_365 : w0 365 = 0 := by
  have hpos : order.symm (875 : Fin 1024) = (365 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_875 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (365 : Fin 1024))]
  exact hs

#print axioms w0_leaf_365
theorem w0_leaf_366 : w0 366 = 0 := by
  have hpos : order.symm (890 : Fin 1024) = (366 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_890 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (366 : Fin 1024))]
  exact hs

#print axioms w0_leaf_366
theorem w0_leaf_367 : w0 367 = 0 := by
  have hpos : order.symm (891 : Fin 1024) = (367 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_891 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (367 : Fin 1024))]
  exact hs

#print axioms w0_leaf_367
theorem w0_leaf_368 : w0 368 = 0 := by
  have hpos : order.symm (906 : Fin 1024) = (368 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_906 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (368 : Fin 1024))]
  exact hs

#print axioms w0_leaf_368
theorem w0_leaf_369 : w0 369 = 0 := by
  have hpos : order.symm (907 : Fin 1024) = (369 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_907 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (369 : Fin 1024))]
  exact hs

#print axioms w0_leaf_369
theorem w0_leaf_370 : w0 370 = 0 := by
  have hpos : order.symm (922 : Fin 1024) = (370 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_922 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (370 : Fin 1024))]
  exact hs

#print axioms w0_leaf_370
theorem w0_leaf_371 : w0 371 = 0 := by
  have hpos : order.symm (923 : Fin 1024) = (371 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_923 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (371 : Fin 1024))]
  exact hs

#print axioms w0_leaf_371
theorem w0_leaf_372 : w0 372 = 0 := by
  have hpos : order.symm (938 : Fin 1024) = (372 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_938 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (372 : Fin 1024))]
  exact hs

#print axioms w0_leaf_372
theorem w0_leaf_373 : w0 373 = 0 := by
  have hpos : order.symm (939 : Fin 1024) = (373 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_939 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (373 : Fin 1024))]
  exact hs

#print axioms w0_leaf_373
theorem w0_leaf_374 : w0 374 = 0 := by
  have hpos : order.symm (954 : Fin 1024) = (374 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_954 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (374 : Fin 1024))]
  exact hs

#print axioms w0_leaf_374
theorem w0_leaf_375 : w0 375 = 0 := by
  have hpos : order.symm (955 : Fin 1024) = (375 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_955 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (375 : Fin 1024))]
  exact hs

#print axioms w0_leaf_375
theorem w0_leaf_376 : w0 376 = 0 := by
  have hpos : order.symm (970 : Fin 1024) = (376 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_970 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (376 : Fin 1024))]
  exact hs

#print axioms w0_leaf_376
theorem w0_leaf_377 : w0 377 = 0 := by
  have hpos : order.symm (971 : Fin 1024) = (377 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_971 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (377 : Fin 1024))]
  exact hs

#print axioms w0_leaf_377
theorem w0_leaf_378 : w0 378 = 0 := by
  have hpos : order.symm (986 : Fin 1024) = (378 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_986 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (378 : Fin 1024))]
  exact hs

#print axioms w0_leaf_378
theorem w0_leaf_379 : w0 379 = 0 := by
  have hpos : order.symm (987 : Fin 1024) = (379 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_987 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (379 : Fin 1024))]
  exact hs

#print axioms w0_leaf_379
theorem w0_leaf_380 : w0 380 = 0 := by
  have hpos : order.symm (1002 : Fin 1024) = (380 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1002 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (380 : Fin 1024))]
  exact hs

#print axioms w0_leaf_380
theorem w0_leaf_381 : w0 381 = 0 := by
  have hpos : order.symm (1003 : Fin 1024) = (381 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_1003 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (381 : Fin 1024))]
  exact hs

#print axioms w0_leaf_381
theorem w0_leaf_382 : w0 382 = 0 := by
  have hpos : order.symm (1018 : Fin 1024) = (382 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1018 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (382 : Fin 1024))]
  exact hs

#print axioms w0_leaf_382
theorem w0_leaf_383 : w0 383 = 0 := by
  have hpos : order.symm (1019 : Fin 1024) = (383 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_1019 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (383 : Fin 1024))]
  exact hs

#print axioms w0_leaf_383
theorem w0_leaf_384 : w0 384 = 0 := by
  have hpos : order.symm (8 : Fin 1024) = (384 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_8 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (384 : Fin 1024))]
  exact hs

#print axioms w0_leaf_384
theorem w0_leaf_385 : w0 385 = 0 := by
  have hpos : order.symm (9 : Fin 1024) = (385 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_9 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (385 : Fin 1024))]
  exact hs

#print axioms w0_leaf_385
theorem w0_leaf_386 : w0 386 = 0 := by
  have hpos : order.symm (24 : Fin 1024) = (386 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_24 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (386 : Fin 1024))]
  exact hs

#print axioms w0_leaf_386
theorem w0_leaf_448 : w0 448 = 0 := by
  have hpos : order.symm (520 : Fin 1024) = (448 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_520 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (448 : Fin 1024))]
  exact hs

#print axioms w0_leaf_448
theorem w0_leaf_449 : w0 449 = 0 := by
  have hpos : order.symm (521 : Fin 1024) = (449 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_521 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (449 : Fin 1024))]
  exact hs

#print axioms w0_leaf_449
theorem w0_leaf_450 : w0 450 = 0 := by
  have hpos : order.symm (536 : Fin 1024) = (450 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_536 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (450 : Fin 1024))]
  exact hs

#print axioms w0_leaf_450
theorem w0_leaf_480 : w0 480 = ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (776 : Fin 1024) = (480 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_776 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (480 : Fin 1024))]
  exact hs

#print axioms w0_leaf_480
theorem w0_leaf_481 : w0 481 = ([1, 1, -1, -2, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (777 : Fin 1024) = (481 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_777 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (481 : Fin 1024))]
  exact hs

#print axioms w0_leaf_481
theorem w0_leaf_482 : w0 482 = ([1, 1, -1, -2, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (792 : Fin 1024) = (482 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_792 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (482 : Fin 1024))]
  exact hs

#print axioms w0_leaf_482
theorem w0_leaf_496 : w0 496 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (904 : Fin 1024) = (496 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_904 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (496 : Fin 1024))]
  exact hs

#print axioms w0_leaf_496
theorem w0_leaf_497 : w0 497 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (905 : Fin 1024) = (497 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_905 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (497 : Fin 1024))]
  exact hs

#print axioms w0_leaf_497
theorem w0_leaf_498 : w0 498 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (920 : Fin 1024) = (498 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_920 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (498 : Fin 1024))]
  exact hs

#print axioms w0_leaf_498
theorem w0_leaf_499 : w0 499 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (921 : Fin 1024) = (499 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_921 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (499 : Fin 1024))]
  exact hs

#print axioms w0_leaf_499
theorem w0_leaf_500 : w0 500 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (936 : Fin 1024) = (500 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_936 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (500 : Fin 1024))]
  exact hs

#print axioms w0_leaf_500
theorem w0_leaf_501 : w0 501 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (937 : Fin 1024) = (501 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_937 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (501 : Fin 1024))]
  exact hs

#print axioms w0_leaf_501
theorem w0_leaf_502 : w0 502 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (952 : Fin 1024) = (502 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_952 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (502 : Fin 1024))]
  exact hs

#print axioms w0_leaf_502
theorem w0_leaf_503 : w0 503 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (953 : Fin 1024) = (503 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_953 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (503 : Fin 1024))]
  exact hs

#print axioms w0_leaf_503
theorem w0_leaf_504 : w0 504 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (968 : Fin 1024) = (504 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_968 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (504 : Fin 1024))]
  exact hs

#print axioms w0_leaf_504
theorem w0_leaf_505 : w0 505 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (969 : Fin 1024) = (505 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_969 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (505 : Fin 1024))]
  exact hs

#print axioms w0_leaf_505
theorem w0_leaf_506 : w0 506 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (984 : Fin 1024) = (506 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_984 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (506 : Fin 1024))]
  exact hs

#print axioms w0_leaf_506
theorem w0_leaf_507 : w0 507 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (985 : Fin 1024) = (507 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_985 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (507 : Fin 1024))]
  exact hs

#print axioms w0_leaf_507
theorem w0_leaf_508 : w0 508 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (1000 : Fin 1024) = (508 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_1000 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (508 : Fin 1024))]
  exact hs

#print axioms w0_leaf_508
theorem w0_leaf_509 : w0 509 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (1001 : Fin 1024) = (509 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1001 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (509 : Fin 1024))]
  exact hs

#print axioms w0_leaf_509
theorem w0_leaf_510 : w0 510 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (1016 : Fin 1024) = (510 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_1016 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (510 : Fin 1024))]
  exact hs

#print axioms w0_leaf_510
theorem w0_leaf_511 : w0 511 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (1017 : Fin 1024) = (511 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1017 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (511 : Fin 1024))]
  exact hs

#print axioms w0_leaf_511
theorem w0_leaf_512 : w0 512 = 0 := by
  have hpos : order.symm (6 : Fin 1024) = (512 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_6 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (512 : Fin 1024))]
  exact hs

#print axioms w0_leaf_512
theorem w0_leaf_513 : w0 513 = 0 := by
  have hpos : order.symm (7 : Fin 1024) = (513 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_7 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (513 : Fin 1024))]
  exact hs

#print axioms w0_leaf_513
theorem w0_leaf_514 : w0 514 = 0 := by
  have hpos : order.symm (22 : Fin 1024) = (514 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_22 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (514 : Fin 1024))]
  exact hs

#print axioms w0_leaf_514
theorem w0_leaf_576 : w0 576 = 0 := by
  have hpos : order.symm (518 : Fin 1024) = (576 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_518 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (576 : Fin 1024))]
  exact hs

#print axioms w0_leaf_576
theorem w0_leaf_577 : w0 577 = 0 := by
  have hpos : order.symm (519 : Fin 1024) = (577 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_519 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (577 : Fin 1024))]
  exact hs

#print axioms w0_leaf_577
theorem w0_leaf_578 : w0 578 = 0 := by
  have hpos : order.symm (534 : Fin 1024) = (578 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_534 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (578 : Fin 1024))]
  exact hs

#print axioms w0_leaf_578
theorem w0_leaf_608 : w0 608 = 0 := by
  have hpos : order.symm (774 : Fin 1024) = (608 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_774 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (608 : Fin 1024))]
  exact hs

#print axioms w0_leaf_608
theorem w0_leaf_609 : w0 609 = 0 := by
  have hpos : order.symm (775 : Fin 1024) = (609 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_775 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (609 : Fin 1024))]
  exact hs

#print axioms w0_leaf_609
theorem w0_leaf_610 : w0 610 = 0 := by
  have hpos : order.symm (790 : Fin 1024) = (610 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_790 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (610 : Fin 1024))]
  exact hs

#print axioms w0_leaf_610
theorem w0_leaf_624 : w0 624 = 0 := by
  have hpos : order.symm (902 : Fin 1024) = (624 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_902 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (624 : Fin 1024))]
  exact hs

#print axioms w0_leaf_624
theorem w0_leaf_625 : w0 625 = 0 := by
  have hpos : order.symm (903 : Fin 1024) = (625 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_903 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (625 : Fin 1024))]
  exact hs

#print axioms w0_leaf_625
theorem w0_leaf_626 : w0 626 = 0 := by
  have hpos : order.symm (918 : Fin 1024) = (626 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_918 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (626 : Fin 1024))]
  exact hs

#print axioms w0_leaf_626
theorem w0_leaf_627 : w0 627 = 0 := by
  have hpos : order.symm (919 : Fin 1024) = (627 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_919 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (627 : Fin 1024))]
  exact hs

#print axioms w0_leaf_627
theorem w0_leaf_628 : w0 628 = 0 := by
  have hpos : order.symm (934 : Fin 1024) = (628 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_934 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (628 : Fin 1024))]
  exact hs

#print axioms w0_leaf_628
theorem w0_leaf_629 : w0 629 = 0 := by
  have hpos : order.symm (935 : Fin 1024) = (629 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_935 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (629 : Fin 1024))]
  exact hs

#print axioms w0_leaf_629
theorem w0_leaf_630 : w0 630 = 0 := by
  have hpos : order.symm (950 : Fin 1024) = (630 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_950 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (630 : Fin 1024))]
  exact hs

#print axioms w0_leaf_630
theorem w0_leaf_631 : w0 631 = 0 := by
  have hpos : order.symm (951 : Fin 1024) = (631 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_951 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (631 : Fin 1024))]
  exact hs

#print axioms w0_leaf_631
theorem w0_leaf_632 : w0 632 = 0 := by
  have hpos : order.symm (966 : Fin 1024) = (632 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_966 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (632 : Fin 1024))]
  exact hs

#print axioms w0_leaf_632
theorem w0_leaf_633 : w0 633 = 0 := by
  have hpos : order.symm (967 : Fin 1024) = (633 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_967 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (633 : Fin 1024))]
  exact hs

#print axioms w0_leaf_633
theorem w0_leaf_634 : w0 634 = 0 := by
  have hpos : order.symm (982 : Fin 1024) = (634 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_982 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (634 : Fin 1024))]
  exact hs

#print axioms w0_leaf_634
theorem w0_leaf_635 : w0 635 = 0 := by
  have hpos : order.symm (983 : Fin 1024) = (635 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_983 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (635 : Fin 1024))]
  exact hs

#print axioms w0_leaf_635
theorem w0_leaf_636 : w0 636 = 0 := by
  have hpos : order.symm (998 : Fin 1024) = (636 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_998 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (636 : Fin 1024))]
  exact hs

#print axioms w0_leaf_636
theorem w0_leaf_637 : w0 637 = 0 := by
  have hpos : order.symm (999 : Fin 1024) = (637 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_999 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (637 : Fin 1024))]
  exact hs

#print axioms w0_leaf_637
theorem w0_leaf_638 : w0 638 = 0 := by
  have hpos : order.symm (1014 : Fin 1024) = (638 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1014 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (638 : Fin 1024))]
  exact hs

#print axioms w0_leaf_638
theorem w0_leaf_639 : w0 639 = 0 := by
  have hpos : order.symm (1015 : Fin 1024) = (639 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1015 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (639 : Fin 1024))]
  exact hs

#print axioms w0_leaf_639
theorem w0_leaf_640 : w0 640 = 0 := by
  have hpos : order.symm (4 : Fin 1024) = (640 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_4 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (640 : Fin 1024))]
  exact hs

#print axioms w0_leaf_640
theorem w0_leaf_641 : w0 641 = 0 := by
  have hpos : order.symm (5 : Fin 1024) = (641 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_5 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (641 : Fin 1024))]
  exact hs

#print axioms w0_leaf_641
theorem w0_leaf_642 : w0 642 = 0 := by
  have hpos : order.symm (20 : Fin 1024) = (642 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_20 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (642 : Fin 1024))]
  exact hs

#print axioms w0_leaf_642
theorem w0_leaf_704 : w0 704 = 0 := by
  have hpos : order.symm (516 : Fin 1024) = (704 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_516 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (704 : Fin 1024))]
  exact hs

#print axioms w0_leaf_704
theorem w0_leaf_736 : w0 736 = ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (772 : Fin 1024) = (736 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_772 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (736 : Fin 1024))]
  exact hs

#print axioms w0_leaf_736
theorem w0_leaf_752 : w0 752 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (900 : Fin 1024) = (752 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_900 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (752 : Fin 1024))]
  exact hs

#print axioms w0_leaf_752
theorem w0_leaf_753 : w0 753 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (901 : Fin 1024) = (753 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_901 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (753 : Fin 1024))]
  exact hs

#print axioms w0_leaf_753
theorem w0_leaf_754 : w0 754 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (916 : Fin 1024) = (754 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_916 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (754 : Fin 1024))]
  exact hs

#print axioms w0_leaf_754
theorem w0_leaf_755 : w0 755 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (917 : Fin 1024) = (755 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_917 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (755 : Fin 1024))]
  exact hs

#print axioms w0_leaf_755
theorem w0_leaf_756 : w0 756 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (932 : Fin 1024) = (756 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_932 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (756 : Fin 1024))]
  exact hs

#print axioms w0_leaf_756
theorem w0_leaf_757 : w0 757 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (933 : Fin 1024) = (757 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_933 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (757 : Fin 1024))]
  exact hs

#print axioms w0_leaf_757
theorem w0_leaf_758 : w0 758 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (948 : Fin 1024) = (758 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_948 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (758 : Fin 1024))]
  exact hs

#print axioms w0_leaf_758
theorem w0_leaf_759 : w0 759 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (949 : Fin 1024) = (759 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_949 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (759 : Fin 1024))]
  exact hs

#print axioms w0_leaf_759
theorem w0_leaf_760 : w0 760 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (964 : Fin 1024) = (760 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_964 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (760 : Fin 1024))]
  exact hs

#print axioms w0_leaf_760
theorem w0_leaf_761 : w0 761 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (965 : Fin 1024) = (761 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_965 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (761 : Fin 1024))]
  exact hs

#print axioms w0_leaf_761
theorem w0_leaf_762 : w0 762 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (980 : Fin 1024) = (762 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_980 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (762 : Fin 1024))]
  exact hs

#print axioms w0_leaf_762
theorem w0_leaf_763 : w0 763 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (981 : Fin 1024) = (763 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_981 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (763 : Fin 1024))]
  exact hs

#print axioms w0_leaf_763
theorem w0_leaf_764 : w0 764 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (996 : Fin 1024) = (764 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_996 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (764 : Fin 1024))]
  exact hs

#print axioms w0_leaf_764
theorem w0_leaf_765 : w0 765 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (997 : Fin 1024) = (765 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_997 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (765 : Fin 1024))]
  exact hs

#print axioms w0_leaf_765
theorem w0_leaf_766 : w0 766 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (1012 : Fin 1024) = (766 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1012 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (766 : Fin 1024))]
  exact hs

#print axioms w0_leaf_766
theorem w0_leaf_767 : w0 767 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (1013 : Fin 1024) = (767 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_1013 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (767 : Fin 1024))]
  exact hs

#print axioms w0_leaf_767
theorem w0_leaf_768 : w0 768 = 0 := by
  have hpos : order.symm (2 : Fin 1024) = (768 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_2 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (768 : Fin 1024))]
  exact hs

#print axioms w0_leaf_768
theorem w0_leaf_832 : w0 832 = 0 := by
  have hpos : order.symm (514 : Fin 1024) = (832 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_514 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (832 : Fin 1024))]
  exact hs

#print axioms w0_leaf_832
theorem w0_leaf_864 : w0 864 = 0 := by
  have hpos : order.symm (770 : Fin 1024) = (864 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_770 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (864 : Fin 1024))]
  exact hs

#print axioms w0_leaf_864
theorem w0_leaf_880 : w0 880 = 0 := by
  have hpos : order.symm (898 : Fin 1024) = (880 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_898 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (880 : Fin 1024))]
  exact hs

#print axioms w0_leaf_880
theorem w0_leaf_881 : w0 881 = 0 := by
  have hpos : order.symm (899 : Fin 1024) = (881 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_899 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (881 : Fin 1024))]
  exact hs

#print axioms w0_leaf_881
theorem w0_leaf_882 : w0 882 = 0 := by
  have hpos : order.symm (914 : Fin 1024) = (882 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_914 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (882 : Fin 1024))]
  exact hs

#print axioms w0_leaf_882
theorem w0_leaf_883 : w0 883 = 0 := by
  have hpos : order.symm (915 : Fin 1024) = (883 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_915 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (883 : Fin 1024))]
  exact hs

#print axioms w0_leaf_883
theorem w0_leaf_884 : w0 884 = 0 := by
  have hpos : order.symm (930 : Fin 1024) = (884 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_930 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (884 : Fin 1024))]
  exact hs

#print axioms w0_leaf_884
theorem w0_leaf_885 : w0 885 = 0 := by
  have hpos : order.symm (931 : Fin 1024) = (885 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_931 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (885 : Fin 1024))]
  exact hs

#print axioms w0_leaf_885
theorem w0_leaf_886 : w0 886 = 0 := by
  have hpos : order.symm (946 : Fin 1024) = (886 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_946 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (886 : Fin 1024))]
  exact hs

#print axioms w0_leaf_886
theorem w0_leaf_887 : w0 887 = 0 := by
  have hpos : order.symm (947 : Fin 1024) = (887 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_947 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (887 : Fin 1024))]
  exact hs

#print axioms w0_leaf_887
theorem w0_leaf_888 : w0 888 = 0 := by
  have hpos : order.symm (962 : Fin 1024) = (888 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_962 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (888 : Fin 1024))]
  exact hs

#print axioms w0_leaf_888
theorem w0_leaf_889 : w0 889 = 0 := by
  have hpos : order.symm (963 : Fin 1024) = (889 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_963 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (889 : Fin 1024))]
  exact hs

#print axioms w0_leaf_889
theorem w0_leaf_890 : w0 890 = 0 := by
  have hpos : order.symm (978 : Fin 1024) = (890 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_978 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (890 : Fin 1024))]
  exact hs

#print axioms w0_leaf_890
theorem w0_leaf_891 : w0 891 = 0 := by
  have hpos : order.symm (979 : Fin 1024) = (891 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_979 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (891 : Fin 1024))]
  exact hs

#print axioms w0_leaf_891
theorem w0_leaf_892 : w0 892 = 0 := by
  have hpos : order.symm (994 : Fin 1024) = (892 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_994 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (892 : Fin 1024))]
  exact hs

#print axioms w0_leaf_892
theorem w0_leaf_893 : w0 893 = 0 := by
  have hpos : order.symm (995 : Fin 1024) = (893 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_995 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (893 : Fin 1024))]
  exact hs

#print axioms w0_leaf_893
theorem w0_leaf_894 : w0 894 = 0 := by
  have hpos : order.symm (1010 : Fin 1024) = (894 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_1010 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (894 : Fin 1024))]
  exact hs

#print axioms w0_leaf_894
theorem w0_leaf_895 : w0 895 = 0 := by
  have hpos : order.symm (1011 : Fin 1024) = (895 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_1011 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (895 : Fin 1024))]
  exact hs

#print axioms w0_leaf_895
theorem w0_leaf_896 : w0 896 = 0 := by
  have hpos : order.symm (0 : Fin 1024) = (896 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_0 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (896 : Fin 1024))]
  exact hs

#print axioms w0_leaf_896
theorem w0_leaf_900 : w0 900 = 0 := by
  have hpos : order.symm (32 : Fin 1024) = (900 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_32 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (900 : Fin 1024))]
  exact hs

#print axioms w0_leaf_900
theorem w0_leaf_901 : w0 901 = 0 := by
  have hpos : order.symm (33 : Fin 1024) = (901 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_33 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (901 : Fin 1024))]
  exact hs

#print axioms w0_leaf_901
theorem w0_leaf_902 : w0 902 = 0 := by
  have hpos : order.symm (48 : Fin 1024) = (902 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_48 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (902 : Fin 1024))]
  exact hs

#print axioms w0_leaf_902
theorem w0_leaf_903 : w0 903 = 0 := by
  have hpos : order.symm (49 : Fin 1024) = (903 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_49 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (903 : Fin 1024))]
  exact hs

#print axioms w0_leaf_903
theorem w0_leaf_904 : w0 904 = 0 := by
  have hpos : order.symm (64 : Fin 1024) = (904 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_64 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (904 : Fin 1024))]
  exact hs

#print axioms w0_leaf_904
theorem w0_leaf_905 : w0 905 = 0 := by
  have hpos : order.symm (65 : Fin 1024) = (905 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_65 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (905 : Fin 1024))]
  exact hs

#print axioms w0_leaf_905
theorem w0_leaf_906 : w0 906 = 0 := by
  have hpos : order.symm (80 : Fin 1024) = (906 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_80 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (906 : Fin 1024))]
  exact hs

#print axioms w0_leaf_906
theorem w0_leaf_907 : w0 907 = 0 := by
  have hpos : order.symm (81 : Fin 1024) = (907 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_81 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (907 : Fin 1024))]
  exact hs

#print axioms w0_leaf_907
theorem w0_leaf_908 : w0 908 = 0 := by
  have hpos : order.symm (96 : Fin 1024) = (908 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_96 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (908 : Fin 1024))]
  exact hs

#print axioms w0_leaf_908
theorem w0_leaf_909 : w0 909 = 0 := by
  have hpos : order.symm (97 : Fin 1024) = (909 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_97 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (909 : Fin 1024))]
  exact hs

#print axioms w0_leaf_909
theorem w0_leaf_910 : w0 910 = 0 := by
  have hpos : order.symm (112 : Fin 1024) = (910 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_112 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (910 : Fin 1024))]
  exact hs

#print axioms w0_leaf_910
theorem w0_leaf_911 : w0 911 = 0 := by
  have hpos : order.symm (113 : Fin 1024) = (911 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_113 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (911 : Fin 1024))]
  exact hs

#print axioms w0_leaf_911
theorem w0_leaf_912 : w0 912 = 0 := by
  have hpos : order.symm (128 : Fin 1024) = (912 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_128 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (912 : Fin 1024))]
  exact hs

#print axioms w0_leaf_912
theorem w0_leaf_913 : w0 913 = 0 := by
  have hpos : order.symm (129 : Fin 1024) = (913 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_129 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (913 : Fin 1024))]
  exact hs

#print axioms w0_leaf_913
theorem w0_leaf_914 : w0 914 = 0 := by
  have hpos : order.symm (144 : Fin 1024) = (914 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_144 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (914 : Fin 1024))]
  exact hs

#print axioms w0_leaf_914
theorem w0_leaf_915 : w0 915 = 0 := by
  have hpos : order.symm (145 : Fin 1024) = (915 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_145 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (915 : Fin 1024))]
  exact hs

#print axioms w0_leaf_915
theorem w0_leaf_916 : w0 916 = 0 := by
  have hpos : order.symm (160 : Fin 1024) = (916 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_160 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (916 : Fin 1024))]
  exact hs

#print axioms w0_leaf_916
theorem w0_leaf_917 : w0 917 = 0 := by
  have hpos : order.symm (161 : Fin 1024) = (917 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_161 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (917 : Fin 1024))]
  exact hs

#print axioms w0_leaf_917
theorem w0_leaf_918 : w0 918 = 0 := by
  have hpos : order.symm (176 : Fin 1024) = (918 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_176 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (918 : Fin 1024))]
  exact hs

#print axioms w0_leaf_918
theorem w0_leaf_919 : w0 919 = 0 := by
  have hpos : order.symm (177 : Fin 1024) = (919 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_177 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (919 : Fin 1024))]
  exact hs

#print axioms w0_leaf_919
theorem w0_leaf_920 : w0 920 = 0 := by
  have hpos : order.symm (192 : Fin 1024) = (920 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_192 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (920 : Fin 1024))]
  exact hs

#print axioms w0_leaf_920
theorem w0_leaf_921 : w0 921 = 0 := by
  have hpos : order.symm (193 : Fin 1024) = (921 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_193 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (921 : Fin 1024))]
  exact hs

#print axioms w0_leaf_921
theorem w0_leaf_922 : w0 922 = 0 := by
  have hpos : order.symm (208 : Fin 1024) = (922 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_208 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (922 : Fin 1024))]
  exact hs

#print axioms w0_leaf_922
theorem w0_leaf_923 : w0 923 = 0 := by
  have hpos : order.symm (209 : Fin 1024) = (923 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_209 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (923 : Fin 1024))]
  exact hs

#print axioms w0_leaf_923
theorem w0_leaf_924 : w0 924 = 0 := by
  have hpos : order.symm (224 : Fin 1024) = (924 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_224 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (924 : Fin 1024))]
  exact hs

#print axioms w0_leaf_924
theorem w0_leaf_925 : w0 925 = 0 := by
  have hpos : order.symm (225 : Fin 1024) = (925 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_225 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (925 : Fin 1024))]
  exact hs

#print axioms w0_leaf_925
theorem w0_leaf_926 : w0 926 = 0 := by
  have hpos : order.symm (240 : Fin 1024) = (926 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_240 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (926 : Fin 1024))]
  exact hs

#print axioms w0_leaf_926
theorem w0_leaf_927 : w0 927 = 0 := by
  have hpos : order.symm (241 : Fin 1024) = (927 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_241 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (927 : Fin 1024))]
  exact hs

#print axioms w0_leaf_927
theorem w0_leaf_928 : w0 928 = 0 := by
  have hpos : order.symm (256 : Fin 1024) = (928 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_256 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (928 : Fin 1024))]
  exact hs

#print axioms w0_leaf_928
theorem w0_leaf_929 : w0 929 = 0 := by
  have hpos : order.symm (257 : Fin 1024) = (929 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_257 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (929 : Fin 1024))]
  exact hs

#print axioms w0_leaf_929
theorem w0_leaf_930 : w0 930 = 0 := by
  have hpos : order.symm (272 : Fin 1024) = (930 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_272 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (930 : Fin 1024))]
  exact hs

#print axioms w0_leaf_930
theorem w0_leaf_931 : w0 931 = 0 := by
  have hpos : order.symm (273 : Fin 1024) = (931 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_273 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (931 : Fin 1024))]
  exact hs

#print axioms w0_leaf_931
theorem w0_leaf_932 : w0 932 = 0 := by
  have hpos : order.symm (288 : Fin 1024) = (932 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_288 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (932 : Fin 1024))]
  exact hs

#print axioms w0_leaf_932
theorem w0_leaf_933 : w0 933 = 0 := by
  have hpos : order.symm (289 : Fin 1024) = (933 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_289 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (933 : Fin 1024))]
  exact hs

#print axioms w0_leaf_933
theorem w0_leaf_934 : w0 934 = 0 := by
  have hpos : order.symm (304 : Fin 1024) = (934 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_304 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (934 : Fin 1024))]
  exact hs

#print axioms w0_leaf_934
theorem w0_leaf_935 : w0 935 = 0 := by
  have hpos : order.symm (305 : Fin 1024) = (935 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_305 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (935 : Fin 1024))]
  exact hs

#print axioms w0_leaf_935
theorem w0_leaf_936 : w0 936 = 0 := by
  have hpos : order.symm (320 : Fin 1024) = (936 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_320 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (936 : Fin 1024))]
  exact hs

#print axioms w0_leaf_936
theorem w0_leaf_937 : w0 937 = 0 := by
  have hpos : order.symm (321 : Fin 1024) = (937 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_321 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (937 : Fin 1024))]
  exact hs

#print axioms w0_leaf_937
theorem w0_leaf_938 : w0 938 = 0 := by
  have hpos : order.symm (336 : Fin 1024) = (938 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_336 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (938 : Fin 1024))]
  exact hs

#print axioms w0_leaf_938
theorem w0_leaf_939 : w0 939 = 0 := by
  have hpos : order.symm (337 : Fin 1024) = (939 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_337 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (939 : Fin 1024))]
  exact hs

#print axioms w0_leaf_939
theorem w0_leaf_940 : w0 940 = 0 := by
  have hpos : order.symm (352 : Fin 1024) = (940 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_352 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (940 : Fin 1024))]
  exact hs

#print axioms w0_leaf_940
theorem w0_leaf_941 : w0 941 = 0 := by
  have hpos : order.symm (353 : Fin 1024) = (941 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_353 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (941 : Fin 1024))]
  exact hs

#print axioms w0_leaf_941
theorem w0_leaf_942 : w0 942 = 0 := by
  have hpos : order.symm (368 : Fin 1024) = (942 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_368 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (942 : Fin 1024))]
  exact hs

#print axioms w0_leaf_942
theorem w0_leaf_943 : w0 943 = 0 := by
  have hpos : order.symm (369 : Fin 1024) = (943 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_369 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (943 : Fin 1024))]
  exact hs

#print axioms w0_leaf_943
theorem w0_leaf_944 : w0 944 = 0 := by
  have hpos : order.symm (384 : Fin 1024) = (944 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_384 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (944 : Fin 1024))]
  exact hs

#print axioms w0_leaf_944
theorem w0_leaf_945 : w0 945 = 0 := by
  have hpos : order.symm (385 : Fin 1024) = (945 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_385 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (945 : Fin 1024))]
  exact hs

#print axioms w0_leaf_945
theorem w0_leaf_946 : w0 946 = 0 := by
  have hpos : order.symm (400 : Fin 1024) = (946 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_400 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (946 : Fin 1024))]
  exact hs

#print axioms w0_leaf_946
theorem w0_leaf_947 : w0 947 = 0 := by
  have hpos : order.symm (401 : Fin 1024) = (947 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_401 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (947 : Fin 1024))]
  exact hs

#print axioms w0_leaf_947
theorem w0_leaf_948 : w0 948 = 0 := by
  have hpos : order.symm (416 : Fin 1024) = (948 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_416 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (948 : Fin 1024))]
  exact hs

#print axioms w0_leaf_948
theorem w0_leaf_949 : w0 949 = 0 := by
  have hpos : order.symm (417 : Fin 1024) = (949 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_417 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (949 : Fin 1024))]
  exact hs

#print axioms w0_leaf_949
theorem w0_leaf_950 : w0 950 = 0 := by
  have hpos : order.symm (432 : Fin 1024) = (950 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_432 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (950 : Fin 1024))]
  exact hs

#print axioms w0_leaf_950
theorem w0_leaf_951 : w0 951 = 0 := by
  have hpos : order.symm (433 : Fin 1024) = (951 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_433 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (951 : Fin 1024))]
  exact hs

#print axioms w0_leaf_951
theorem w0_leaf_952 : w0 952 = 0 := by
  have hpos : order.symm (448 : Fin 1024) = (952 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_448 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (952 : Fin 1024))]
  exact hs

#print axioms w0_leaf_952
theorem w0_leaf_953 : w0 953 = 0 := by
  have hpos : order.symm (449 : Fin 1024) = (953 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_449 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (953 : Fin 1024))]
  exact hs

#print axioms w0_leaf_953
theorem w0_leaf_954 : w0 954 = 0 := by
  have hpos : order.symm (464 : Fin 1024) = (954 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_464 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (954 : Fin 1024))]
  exact hs

#print axioms w0_leaf_954
theorem w0_leaf_955 : w0 955 = 0 := by
  have hpos : order.symm (465 : Fin 1024) = (955 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_465 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (955 : Fin 1024))]
  exact hs

#print axioms w0_leaf_955
theorem w0_leaf_956 : w0 956 = 0 := by
  have hpos : order.symm (480 : Fin 1024) = (956 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_480 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (956 : Fin 1024))]
  exact hs

#print axioms w0_leaf_956
theorem w0_leaf_957 : w0 957 = 0 := by
  have hpos : order.symm (481 : Fin 1024) = (957 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_481 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (957 : Fin 1024))]
  exact hs

#print axioms w0_leaf_957
theorem w0_leaf_958 : w0 958 = 0 := by
  have hpos : order.symm (496 : Fin 1024) = (958 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_496 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (958 : Fin 1024))]
  exact hs

#print axioms w0_leaf_958
theorem w0_leaf_959 : w0 959 = 0 := by
  have hpos : order.symm (497 : Fin 1024) = (959 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_497 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (959 : Fin 1024))]
  exact hs

#print axioms w0_leaf_959
theorem w0_leaf_960 : w0 960 = 0 := by
  have hpos : order.symm (512 : Fin 1024) = (960 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_512 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (960 : Fin 1024))]
  exact hs

#print axioms w0_leaf_960
theorem w0_leaf_961 : w0 961 = 0 := by
  have hpos : order.symm (513 : Fin 1024) = (961 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_513 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (961 : Fin 1024))]
  exact hs

#print axioms w0_leaf_961
theorem w0_leaf_962 : w0 962 = 0 := by
  have hpos : order.symm (528 : Fin 1024) = (962 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_528 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (962 : Fin 1024))]
  exact hs

#print axioms w0_leaf_962
theorem w0_leaf_963 : w0 963 = 0 := by
  have hpos : order.symm (529 : Fin 1024) = (963 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_529 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (963 : Fin 1024))]
  exact hs

#print axioms w0_leaf_963
theorem w0_leaf_964 : w0 964 = 0 := by
  have hpos : order.symm (544 : Fin 1024) = (964 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_544 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (964 : Fin 1024))]
  exact hs

#print axioms w0_leaf_964
theorem w0_leaf_965 : w0 965 = 0 := by
  have hpos : order.symm (545 : Fin 1024) = (965 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_545 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (965 : Fin 1024))]
  exact hs

#print axioms w0_leaf_965
theorem w0_leaf_966 : w0 966 = 0 := by
  have hpos : order.symm (560 : Fin 1024) = (966 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_560 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (966 : Fin 1024))]
  exact hs

#print axioms w0_leaf_966
theorem w0_leaf_967 : w0 967 = 0 := by
  have hpos : order.symm (561 : Fin 1024) = (967 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_561 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (967 : Fin 1024))]
  exact hs

#print axioms w0_leaf_967
theorem w0_leaf_968 : w0 968 = 0 := by
  have hpos : order.symm (576 : Fin 1024) = (968 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_576 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (968 : Fin 1024))]
  exact hs

#print axioms w0_leaf_968
theorem w0_leaf_969 : w0 969 = 0 := by
  have hpos : order.symm (577 : Fin 1024) = (969 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_577 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (969 : Fin 1024))]
  exact hs

#print axioms w0_leaf_969
theorem w0_leaf_970 : w0 970 = 0 := by
  have hpos : order.symm (592 : Fin 1024) = (970 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_592 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (970 : Fin 1024))]
  exact hs

#print axioms w0_leaf_970
theorem w0_leaf_971 : w0 971 = 0 := by
  have hpos : order.symm (593 : Fin 1024) = (971 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_593 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (971 : Fin 1024))]
  exact hs

#print axioms w0_leaf_971
theorem w0_leaf_972 : w0 972 = 0 := by
  have hpos : order.symm (608 : Fin 1024) = (972 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_608 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (972 : Fin 1024))]
  exact hs

#print axioms w0_leaf_972
theorem w0_leaf_973 : w0 973 = 0 := by
  have hpos : order.symm (609 : Fin 1024) = (973 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_609 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (973 : Fin 1024))]
  exact hs

#print axioms w0_leaf_973
theorem w0_leaf_974 : w0 974 = 0 := by
  have hpos : order.symm (624 : Fin 1024) = (974 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_624 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (974 : Fin 1024))]
  exact hs

#print axioms w0_leaf_974
theorem w0_leaf_975 : w0 975 = 0 := by
  have hpos : order.symm (625 : Fin 1024) = (975 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_625 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (975 : Fin 1024))]
  exact hs

#print axioms w0_leaf_975
theorem w0_leaf_976 : w0 976 = 0 := by
  have hpos : order.symm (640 : Fin 1024) = (976 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_640 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (976 : Fin 1024))]
  exact hs

#print axioms w0_leaf_976
theorem w0_leaf_977 : w0 977 = 0 := by
  have hpos : order.symm (641 : Fin 1024) = (977 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_641 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (977 : Fin 1024))]
  exact hs

#print axioms w0_leaf_977
theorem w0_leaf_978 : w0 978 = 0 := by
  have hpos : order.symm (656 : Fin 1024) = (978 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_656 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (978 : Fin 1024))]
  exact hs

#print axioms w0_leaf_978
theorem w0_leaf_979 : w0 979 = 0 := by
  have hpos : order.symm (657 : Fin 1024) = (979 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_657 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (979 : Fin 1024))]
  exact hs

#print axioms w0_leaf_979
theorem w0_leaf_980 : w0 980 = 0 := by
  have hpos : order.symm (672 : Fin 1024) = (980 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_672 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (980 : Fin 1024))]
  exact hs

#print axioms w0_leaf_980
theorem w0_leaf_981 : w0 981 = 0 := by
  have hpos : order.symm (673 : Fin 1024) = (981 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_673 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (981 : Fin 1024))]
  exact hs

#print axioms w0_leaf_981
theorem w0_leaf_982 : w0 982 = 0 := by
  have hpos : order.symm (688 : Fin 1024) = (982 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_688 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (982 : Fin 1024))]
  exact hs

#print axioms w0_leaf_982
theorem w0_leaf_983 : w0 983 = 0 := by
  have hpos : order.symm (689 : Fin 1024) = (983 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_689 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (983 : Fin 1024))]
  exact hs

#print axioms w0_leaf_983
theorem w0_leaf_984 : w0 984 = 0 := by
  have hpos : order.symm (704 : Fin 1024) = (984 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_704 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (984 : Fin 1024))]
  exact hs

#print axioms w0_leaf_984
theorem w0_leaf_985 : w0 985 = 0 := by
  have hpos : order.symm (705 : Fin 1024) = (985 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_705 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (985 : Fin 1024))]
  exact hs

#print axioms w0_leaf_985
theorem w0_leaf_986 : w0 986 = 0 := by
  have hpos : order.symm (720 : Fin 1024) = (986 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_720 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (986 : Fin 1024))]
  exact hs

#print axioms w0_leaf_986
theorem w0_leaf_987 : w0 987 = 0 := by
  have hpos : order.symm (721 : Fin 1024) = (987 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_721 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (987 : Fin 1024))]
  exact hs

#print axioms w0_leaf_987
theorem w0_leaf_988 : w0 988 = 0 := by
  have hpos : order.symm (736 : Fin 1024) = (988 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_zero_original_736 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (988 : Fin 1024))]
  exact hs

#print axioms w0_leaf_988
theorem w0_leaf_989 : w0 989 = 0 := by
  have hpos : order.symm (737 : Fin 1024) = (989 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_737 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (989 : Fin 1024))]
  exact hs

#print axioms w0_leaf_989
theorem w0_leaf_990 : w0 990 = 0 := by
  have hpos : order.symm (752 : Fin 1024) = (990 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_zero_original_752 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (990 : Fin 1024))]
  exact hs

#print axioms w0_leaf_990
theorem w0_leaf_991 : w0 991 = 0 := by
  have hpos : order.symm (753 : Fin 1024) = (991 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_753 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (991 : Fin 1024))]
  exact hs

#print axioms w0_leaf_991
theorem w0_leaf_992 : w0 992 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (768 : Fin 1024) = (992 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_768 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (992 : Fin 1024))]
  exact hs

#print axioms w0_leaf_992
theorem w0_leaf_993 : w0 993 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (769 : Fin 1024) = (993 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_769 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (993 : Fin 1024))]
  exact hs

#print axioms w0_leaf_993
theorem w0_leaf_994 : w0 994 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (784 : Fin 1024) = (994 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_784 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (994 : Fin 1024))]
  exact hs

#print axioms w0_leaf_994
theorem w0_leaf_995 : w0 995 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (785 : Fin 1024) = (995 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_785 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (995 : Fin 1024))]
  exact hs

#print axioms w0_leaf_995
theorem w0_leaf_996 : w0 996 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (800 : Fin 1024) = (996 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_800 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (996 : Fin 1024))]
  exact hs

#print axioms w0_leaf_996
theorem w0_leaf_997 : w0 997 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (801 : Fin 1024) = (997 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_801 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (997 : Fin 1024))]
  exact hs

#print axioms w0_leaf_997
theorem w0_leaf_998 : w0 998 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (816 : Fin 1024) = (998 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_816 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (998 : Fin 1024))]
  exact hs

#print axioms w0_leaf_998
theorem w0_leaf_999 : w0 999 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (817 : Fin 1024) = (999 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_817 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (999 : Fin 1024))]
  exact hs

#print axioms w0_leaf_999
theorem w0_leaf_1000 : w0 1000 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (832 : Fin 1024) = (1000 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_832 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1000 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1000
theorem w0_leaf_1001 : w0 1001 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (833 : Fin 1024) = (1001 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_833 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1001 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1001
theorem w0_leaf_1002 : w0 1002 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (848 : Fin 1024) = (1002 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_848 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1002 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1002
theorem w0_leaf_1003 : w0 1003 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (849 : Fin 1024) = (1003 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_849 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1003 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1003
theorem w0_leaf_1004 : w0 1004 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (864 : Fin 1024) = (1004 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_864 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1004 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1004
theorem w0_leaf_1005 : w0 1005 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (865 : Fin 1024) = (1005 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_865 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1005 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1005
theorem w0_leaf_1006 : w0 1006 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (880 : Fin 1024) = (1006 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_880 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1006 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1006
theorem w0_leaf_1007 : w0 1007 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (881 : Fin 1024) = (1007 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_881 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1007 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1007
theorem w0_leaf_1008 : w0 1008 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (896 : Fin 1024) = (1008 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_896 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1008 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1008
theorem w0_leaf_1009 : w0 1009 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (897 : Fin 1024) = (1009 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_897 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1009 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1009
theorem w0_leaf_1010 : w0 1010 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (912 : Fin 1024) = (1010 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_912 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1010 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1010
theorem w0_leaf_1011 : w0 1011 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (913 : Fin 1024) = (1011 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_913 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1011 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1011
theorem w0_leaf_1012 : w0 1012 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (928 : Fin 1024) = (1012 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_928 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1012 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1012
theorem w0_leaf_1013 : w0 1013 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (929 : Fin 1024) = (1013 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_929 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1013 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1013
theorem w0_leaf_1014 : w0 1014 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (944 : Fin 1024) = (1014 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_944 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1014 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1014
theorem w0_leaf_1015 : w0 1015 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (945 : Fin 1024) = (1015 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_945 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1015 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1015
theorem w0_leaf_1016 : w0 1016 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (960 : Fin 1024) = (1016 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_960 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1016 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1016
theorem w0_leaf_1017 : w0 1017 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (961 : Fin 1024) = (1017 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_961 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1017 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1017
theorem w0_leaf_1018 : w0 1018 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (976 : Fin 1024) = (1018 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_976 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1018 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1018
theorem w0_leaf_1019 : w0 1019 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (977 : Fin 1024) = (1019 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_977 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1019 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1019
theorem w0_leaf_1020 : w0 1020 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (992 : Fin 1024) = (1020 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_992 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1020 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1020
theorem w0_leaf_1021 : w0 1021 = 0 := by
  have hpos : order.symm (1022 : Fin 1024) = (1021 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_1022 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1021 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1021
theorem w0_leaf_1022 : w0 1022 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (1008 : Fin 1024) = (1022 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_1008 (F := M)
  rw [← hpos] at hs
  rw [w0_at (i := (1022 : Fin 1024))]
  exact hs

#print axioms w0_leaf_1022
theorem w2_leaf_0 : w2 0 = 0 := by
  have hpos : order.symm (14 : Fin 1024) = (0 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeaves.point2_guard14_transport_zero (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (0 : Fin 1024))]
  exact hs

#print axioms w2_leaf_0
theorem w2_leaf_1 : w2 1 = 0 := by
  have hpos : order.symm (15 : Fin 1024) = (1 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_15 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1
theorem w2_leaf_2 : w2 2 = 0 := by
  have hpos : order.symm (30 : Fin 1024) = (2 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_30 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (2 : Fin 1024))]
  exact hs

#print axioms w2_leaf_2
theorem w2_leaf_3 : w2 3 = 0 := by
  have hpos : order.symm (31 : Fin 1024) = (3 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_31 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (3 : Fin 1024))]
  exact hs

#print axioms w2_leaf_3
theorem w2_leaf_4 : w2 4 = 0 := by
  have hpos : order.symm (46 : Fin 1024) = (4 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_46 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (4 : Fin 1024))]
  exact hs

#print axioms w2_leaf_4
theorem w2_leaf_5 : w2 5 = 0 := by
  have hpos : order.symm (47 : Fin 1024) = (5 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_47 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (5 : Fin 1024))]
  exact hs

#print axioms w2_leaf_5
theorem w2_leaf_6 : w2 6 = 0 := by
  have hpos : order.symm (62 : Fin 1024) = (6 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_62 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (6 : Fin 1024))]
  exact hs

#print axioms w2_leaf_6
theorem w2_leaf_64 : w2 64 = 0 := by
  have hpos : order.symm (526 : Fin 1024) = (64 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_526 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (64 : Fin 1024))]
  exact hs

#print axioms w2_leaf_64
theorem w2_leaf_65 : w2 65 = 0 := by
  have hpos : order.symm (527 : Fin 1024) = (65 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_527 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (65 : Fin 1024))]
  exact hs

#print axioms w2_leaf_65
theorem w2_leaf_66 : w2 66 = 0 := by
  have hpos : order.symm (542 : Fin 1024) = (66 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_542 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (66 : Fin 1024))]
  exact hs

#print axioms w2_leaf_66
theorem w2_leaf_80 : w2 80 = 0 := by
  have hpos : order.symm (654 : Fin 1024) = (80 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_654 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (80 : Fin 1024))]
  exact hs

#print axioms w2_leaf_80
theorem w2_leaf_81 : w2 81 = 0 := by
  have hpos : order.symm (655 : Fin 1024) = (81 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_655 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (81 : Fin 1024))]
  exact hs

#print axioms w2_leaf_81
theorem w2_leaf_82 : w2 82 = 0 := by
  have hpos : order.symm (670 : Fin 1024) = (82 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_670 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (82 : Fin 1024))]
  exact hs

#print axioms w2_leaf_82
theorem w2_leaf_88 : w2 88 = 0 := by
  have hpos : order.symm (718 : Fin 1024) = (88 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_718 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (88 : Fin 1024))]
  exact hs

#print axioms w2_leaf_88
theorem w2_leaf_89 : w2 89 = 0 := by
  have hpos : order.symm (719 : Fin 1024) = (89 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_719 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (89 : Fin 1024))]
  exact hs

#print axioms w2_leaf_89
theorem w2_leaf_90 : w2 90 = 0 := by
  have hpos : order.symm (734 : Fin 1024) = (90 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_734 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (90 : Fin 1024))]
  exact hs

#print axioms w2_leaf_90
theorem w2_leaf_92 : w2 92 = 0 := by
  have hpos : order.symm (750 : Fin 1024) = (92 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_750 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (92 : Fin 1024))]
  exact hs

#print axioms w2_leaf_92
theorem w2_leaf_93 : w2 93 = 0 := by
  have hpos : order.symm (751 : Fin 1024) = (93 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_751 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (93 : Fin 1024))]
  exact hs

#print axioms w2_leaf_93
theorem w2_leaf_94 : w2 94 = 0 := by
  have hpos : order.symm (766 : Fin 1024) = (94 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_766 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (94 : Fin 1024))]
  exact hs

#print axioms w2_leaf_94
theorem w2_leaf_95 : w2 95 = 0 := by
  have hpos : order.symm (767 : Fin 1024) = (95 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_767 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (95 : Fin 1024))]
  exact hs

#print axioms w2_leaf_95
theorem w2_leaf_96 : w2 96 = 0 := by
  have hpos : order.symm (782 : Fin 1024) = (96 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_782 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (96 : Fin 1024))]
  exact hs

#print axioms w2_leaf_96
theorem w2_leaf_97 : w2 97 = 0 := by
  have hpos : order.symm (783 : Fin 1024) = (97 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_783 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (97 : Fin 1024))]
  exact hs

#print axioms w2_leaf_97
theorem w2_leaf_98 : w2 98 = 0 := by
  have hpos : order.symm (798 : Fin 1024) = (98 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_798 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (98 : Fin 1024))]
  exact hs

#print axioms w2_leaf_98
theorem w2_leaf_99 : w2 99 = 0 := by
  have hpos : order.symm (799 : Fin 1024) = (99 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_799 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (99 : Fin 1024))]
  exact hs

#print axioms w2_leaf_99
theorem w2_leaf_100 : w2 100 = 0 := by
  have hpos : order.symm (814 : Fin 1024) = (100 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_814 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (100 : Fin 1024))]
  exact hs

#print axioms w2_leaf_100
theorem w2_leaf_101 : w2 101 = 0 := by
  have hpos : order.symm (815 : Fin 1024) = (101 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_815 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (101 : Fin 1024))]
  exact hs

#print axioms w2_leaf_101
theorem w2_leaf_102 : w2 102 = 0 := by
  have hpos : order.symm (830 : Fin 1024) = (102 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_830 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (102 : Fin 1024))]
  exact hs

#print axioms w2_leaf_102
theorem w2_leaf_105 : w2 105 = 0 := by
  have hpos : order.symm (847 : Fin 1024) = (105 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_847 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (105 : Fin 1024))]
  exact hs

#print axioms w2_leaf_105
theorem w2_leaf_106 : w2 106 = 0 := by
  have hpos : order.symm (862 : Fin 1024) = (106 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_862 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (106 : Fin 1024))]
  exact hs

#print axioms w2_leaf_106
theorem w2_leaf_108 : w2 108 = 0 := by
  have hpos : order.symm (878 : Fin 1024) = (108 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_878 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (108 : Fin 1024))]
  exact hs

#print axioms w2_leaf_108
theorem w2_leaf_109 : w2 109 = 0 := by
  have hpos : order.symm (879 : Fin 1024) = (109 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_879 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (109 : Fin 1024))]
  exact hs

#print axioms w2_leaf_109
theorem w2_leaf_110 : w2 110 = 0 := by
  have hpos : order.symm (894 : Fin 1024) = (110 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_894 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (110 : Fin 1024))]
  exact hs

#print axioms w2_leaf_110
theorem w2_leaf_111 : w2 111 = 0 := by
  have hpos : order.symm (895 : Fin 1024) = (111 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_895 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (111 : Fin 1024))]
  exact hs

#print axioms w2_leaf_111
theorem w2_leaf_112 : w2 112 = 0 := by
  have hpos : order.symm (910 : Fin 1024) = (112 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_910 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (112 : Fin 1024))]
  exact hs

#print axioms w2_leaf_112
theorem w2_leaf_113 : w2 113 = 0 := by
  have hpos : order.symm (911 : Fin 1024) = (113 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_911 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (113 : Fin 1024))]
  exact hs

#print axioms w2_leaf_113
theorem w2_leaf_114 : w2 114 = 0 := by
  have hpos : order.symm (926 : Fin 1024) = (114 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_926 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (114 : Fin 1024))]
  exact hs

#print axioms w2_leaf_114
theorem w2_leaf_115 : w2 115 = 0 := by
  have hpos : order.symm (927 : Fin 1024) = (115 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_927 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (115 : Fin 1024))]
  exact hs

#print axioms w2_leaf_115
theorem w2_leaf_116 : w2 116 = 0 := by
  have hpos : order.symm (942 : Fin 1024) = (116 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_942 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (116 : Fin 1024))]
  exact hs

#print axioms w2_leaf_116
theorem w2_leaf_117 : w2 117 = 0 := by
  have hpos : order.symm (943 : Fin 1024) = (117 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_943 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (117 : Fin 1024))]
  exact hs

#print axioms w2_leaf_117
theorem w2_leaf_118 : w2 118 = 0 := by
  have hpos : order.symm (958 : Fin 1024) = (118 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_958 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (118 : Fin 1024))]
  exact hs

#print axioms w2_leaf_118
theorem w2_leaf_119 : w2 119 = 0 := by
  have hpos : order.symm (959 : Fin 1024) = (119 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_959 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (119 : Fin 1024))]
  exact hs

#print axioms w2_leaf_119
theorem w2_leaf_120 : w2 120 = 0 := by
  have hpos : order.symm (974 : Fin 1024) = (120 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_974 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (120 : Fin 1024))]
  exact hs

#print axioms w2_leaf_120
theorem w2_leaf_121 : w2 121 = 0 := by
  have hpos : order.symm (975 : Fin 1024) = (121 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_975 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (121 : Fin 1024))]
  exact hs

#print axioms w2_leaf_121
theorem w2_leaf_122 : w2 122 = 0 := by
  have hpos : order.symm (990 : Fin 1024) = (122 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_990 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (122 : Fin 1024))]
  exact hs

#print axioms w2_leaf_122
theorem w2_leaf_123 : w2 123 = 0 := by
  have hpos : order.symm (991 : Fin 1024) = (123 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_991 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (123 : Fin 1024))]
  exact hs

#print axioms w2_leaf_123
theorem w2_leaf_124 : w2 124 = 0 := by
  have hpos : order.symm (1006 : Fin 1024) = (124 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_1006 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (124 : Fin 1024))]
  exact hs

#print axioms w2_leaf_124
theorem w2_leaf_125 : w2 125 = 0 := by
  have hpos : order.symm (1007 : Fin 1024) = (125 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_1007 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (125 : Fin 1024))]
  exact hs

#print axioms w2_leaf_125
theorem w2_leaf_126 : w2 126 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (993 : Fin 1024) = (126 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_993 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (126 : Fin 1024))]
  exact hs

#print axioms w2_leaf_126
theorem w2_leaf_127 : w2 127 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (1009 : Fin 1024) = (127 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_1009 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (127 : Fin 1024))]
  exact hs

#print axioms w2_leaf_127
theorem w2_leaf_128 : w2 128 = 0 := by
  have hpos : order.symm (12 : Fin 1024) = (128 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_12 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (128 : Fin 1024))]
  exact hs

#print axioms w2_leaf_128
theorem w2_leaf_129 : w2 129 = 0 := by
  have hpos : order.symm (13 : Fin 1024) = (129 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_13 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (129 : Fin 1024))]
  exact hs

#print axioms w2_leaf_129
theorem w2_leaf_130 : w2 130 = 0 := by
  have hpos : order.symm (28 : Fin 1024) = (130 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_28 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (130 : Fin 1024))]
  exact hs

#print axioms w2_leaf_130
theorem w2_leaf_131 : w2 131 = 0 := by
  have hpos : order.symm (29 : Fin 1024) = (131 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_29 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (131 : Fin 1024))]
  exact hs

#print axioms w2_leaf_131
theorem w2_leaf_132 : w2 132 = 0 := by
  have hpos : order.symm (44 : Fin 1024) = (132 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_44 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (132 : Fin 1024))]
  exact hs

#print axioms w2_leaf_132
theorem w2_leaf_133 : w2 133 = 0 := by
  have hpos : order.symm (45 : Fin 1024) = (133 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_45 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (133 : Fin 1024))]
  exact hs

#print axioms w2_leaf_133
theorem w2_leaf_134 : w2 134 = 0 := by
  have hpos : order.symm (60 : Fin 1024) = (134 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_60 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (134 : Fin 1024))]
  exact hs

#print axioms w2_leaf_134
theorem w2_leaf_135 : w2 135 = 0 := by
  have hpos : order.symm (61 : Fin 1024) = (135 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_61 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (135 : Fin 1024))]
  exact hs

#print axioms w2_leaf_135
theorem w2_leaf_136 : w2 136 = 0 := by
  have hpos : order.symm (76 : Fin 1024) = (136 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_76 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (136 : Fin 1024))]
  exact hs

#print axioms w2_leaf_136
theorem w2_leaf_137 : w2 137 = 0 := by
  have hpos : order.symm (77 : Fin 1024) = (137 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_77 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (137 : Fin 1024))]
  exact hs

#print axioms w2_leaf_137
theorem w2_leaf_138 : w2 138 = 0 := by
  have hpos : order.symm (92 : Fin 1024) = (138 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_92 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (138 : Fin 1024))]
  exact hs

#print axioms w2_leaf_138
theorem w2_leaf_139 : w2 139 = 0 := by
  have hpos : order.symm (93 : Fin 1024) = (139 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_93 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (139 : Fin 1024))]
  exact hs

#print axioms w2_leaf_139
theorem w2_leaf_140 : w2 140 = 0 := by
  have hpos : order.symm (108 : Fin 1024) = (140 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_108 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (140 : Fin 1024))]
  exact hs

#print axioms w2_leaf_140
theorem w2_leaf_141 : w2 141 = 0 := by
  have hpos : order.symm (109 : Fin 1024) = (141 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_109 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (141 : Fin 1024))]
  exact hs

#print axioms w2_leaf_141
theorem w2_leaf_142 : w2 142 = 0 := by
  have hpos : order.symm (124 : Fin 1024) = (142 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_124 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (142 : Fin 1024))]
  exact hs

#print axioms w2_leaf_142
theorem w2_leaf_143 : w2 143 = 0 := by
  have hpos : order.symm (125 : Fin 1024) = (143 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_125 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (143 : Fin 1024))]
  exact hs

#print axioms w2_leaf_143
theorem w2_leaf_144 : w2 144 = 0 := by
  have hpos : order.symm (140 : Fin 1024) = (144 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_140 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (144 : Fin 1024))]
  exact hs

#print axioms w2_leaf_144
theorem w2_leaf_145 : w2 145 = 0 := by
  have hpos : order.symm (141 : Fin 1024) = (145 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_141 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (145 : Fin 1024))]
  exact hs

#print axioms w2_leaf_145
theorem w2_leaf_146 : w2 146 = 0 := by
  have hpos : order.symm (156 : Fin 1024) = (146 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_156 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (146 : Fin 1024))]
  exact hs

#print axioms w2_leaf_146
theorem w2_leaf_147 : w2 147 = 0 := by
  have hpos : order.symm (157 : Fin 1024) = (147 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_157 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (147 : Fin 1024))]
  exact hs

#print axioms w2_leaf_147
theorem w2_leaf_148 : w2 148 = 0 := by
  have hpos : order.symm (172 : Fin 1024) = (148 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_172 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (148 : Fin 1024))]
  exact hs

#print axioms w2_leaf_148
theorem w2_leaf_149 : w2 149 = 0 := by
  have hpos : order.symm (173 : Fin 1024) = (149 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_173 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (149 : Fin 1024))]
  exact hs

#print axioms w2_leaf_149
theorem w2_leaf_150 : w2 150 = 0 := by
  have hpos : order.symm (188 : Fin 1024) = (150 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_188 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (150 : Fin 1024))]
  exact hs

#print axioms w2_leaf_150
theorem w2_leaf_151 : w2 151 = 0 := by
  have hpos : order.symm (189 : Fin 1024) = (151 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_189 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (151 : Fin 1024))]
  exact hs

#print axioms w2_leaf_151
theorem w2_leaf_152 : w2 152 = 0 := by
  have hpos : order.symm (204 : Fin 1024) = (152 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_204 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (152 : Fin 1024))]
  exact hs

#print axioms w2_leaf_152
theorem w2_leaf_153 : w2 153 = 0 := by
  have hpos : order.symm (205 : Fin 1024) = (153 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_205 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (153 : Fin 1024))]
  exact hs

#print axioms w2_leaf_153
theorem w2_leaf_154 : w2 154 = 0 := by
  have hpos : order.symm (220 : Fin 1024) = (154 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_220 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (154 : Fin 1024))]
  exact hs

#print axioms w2_leaf_154
theorem w2_leaf_155 : w2 155 = 0 := by
  have hpos : order.symm (221 : Fin 1024) = (155 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_221 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (155 : Fin 1024))]
  exact hs

#print axioms w2_leaf_155
theorem w2_leaf_156 : w2 156 = 0 := by
  have hpos : order.symm (236 : Fin 1024) = (156 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_236 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (156 : Fin 1024))]
  exact hs

#print axioms w2_leaf_156
theorem w2_leaf_157 : w2 157 = 0 := by
  have hpos : order.symm (237 : Fin 1024) = (157 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_237 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (157 : Fin 1024))]
  exact hs

#print axioms w2_leaf_157
theorem w2_leaf_158 : w2 158 = 0 := by
  have hpos : order.symm (252 : Fin 1024) = (158 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_252 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (158 : Fin 1024))]
  exact hs

#print axioms w2_leaf_158
theorem w2_leaf_159 : w2 159 = 0 := by
  have hpos : order.symm (253 : Fin 1024) = (159 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_253 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (159 : Fin 1024))]
  exact hs

#print axioms w2_leaf_159
theorem w2_leaf_160 : w2 160 = 0 := by
  have hpos : order.symm (268 : Fin 1024) = (160 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_268 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (160 : Fin 1024))]
  exact hs

#print axioms w2_leaf_160
theorem w2_leaf_161 : w2 161 = 0 := by
  have hpos : order.symm (269 : Fin 1024) = (161 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_269 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (161 : Fin 1024))]
  exact hs

#print axioms w2_leaf_161
theorem w2_leaf_162 : w2 162 = 0 := by
  have hpos : order.symm (284 : Fin 1024) = (162 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_284 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (162 : Fin 1024))]
  exact hs

#print axioms w2_leaf_162
theorem w2_leaf_163 : w2 163 = 0 := by
  have hpos : order.symm (285 : Fin 1024) = (163 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_285 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (163 : Fin 1024))]
  exact hs

#print axioms w2_leaf_163
theorem w2_leaf_164 : w2 164 = 0 := by
  have hpos : order.symm (300 : Fin 1024) = (164 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_300 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (164 : Fin 1024))]
  exact hs

#print axioms w2_leaf_164
theorem w2_leaf_165 : w2 165 = 0 := by
  have hpos : order.symm (301 : Fin 1024) = (165 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_301 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (165 : Fin 1024))]
  exact hs

#print axioms w2_leaf_165
theorem w2_leaf_166 : w2 166 = 0 := by
  have hpos : order.symm (316 : Fin 1024) = (166 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_316 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (166 : Fin 1024))]
  exact hs

#print axioms w2_leaf_166
theorem w2_leaf_167 : w2 167 = 0 := by
  have hpos : order.symm (317 : Fin 1024) = (167 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_317 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (167 : Fin 1024))]
  exact hs

#print axioms w2_leaf_167
theorem w2_leaf_168 : w2 168 = 0 := by
  have hpos : order.symm (332 : Fin 1024) = (168 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_332 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (168 : Fin 1024))]
  exact hs

#print axioms w2_leaf_168
theorem w2_leaf_169 : w2 169 = 0 := by
  have hpos : order.symm (333 : Fin 1024) = (169 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_333 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (169 : Fin 1024))]
  exact hs

#print axioms w2_leaf_169
theorem w2_leaf_170 : w2 170 = 0 := by
  have hpos : order.symm (348 : Fin 1024) = (170 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_348 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (170 : Fin 1024))]
  exact hs

#print axioms w2_leaf_170
theorem w2_leaf_171 : w2 171 = 0 := by
  have hpos : order.symm (349 : Fin 1024) = (171 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_349 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (171 : Fin 1024))]
  exact hs

#print axioms w2_leaf_171
theorem w2_leaf_172 : w2 172 = 0 := by
  have hpos : order.symm (364 : Fin 1024) = (172 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_364 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (172 : Fin 1024))]
  exact hs

#print axioms w2_leaf_172
theorem w2_leaf_173 : w2 173 = 0 := by
  have hpos : order.symm (365 : Fin 1024) = (173 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_365 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (173 : Fin 1024))]
  exact hs

#print axioms w2_leaf_173
theorem w2_leaf_174 : w2 174 = 0 := by
  have hpos : order.symm (380 : Fin 1024) = (174 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_380 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (174 : Fin 1024))]
  exact hs

#print axioms w2_leaf_174
theorem w2_leaf_175 : w2 175 = 0 := by
  have hpos : order.symm (381 : Fin 1024) = (175 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_381 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (175 : Fin 1024))]
  exact hs

#print axioms w2_leaf_175
theorem w2_leaf_176 : w2 176 = 0 := by
  have hpos : order.symm (396 : Fin 1024) = (176 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_396 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (176 : Fin 1024))]
  exact hs

#print axioms w2_leaf_176
theorem w2_leaf_177 : w2 177 = 0 := by
  have hpos : order.symm (397 : Fin 1024) = (177 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_397 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (177 : Fin 1024))]
  exact hs

#print axioms w2_leaf_177
theorem w2_leaf_178 : w2 178 = 0 := by
  have hpos : order.symm (412 : Fin 1024) = (178 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_412 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (178 : Fin 1024))]
  exact hs

#print axioms w2_leaf_178
theorem w2_leaf_179 : w2 179 = 0 := by
  have hpos : order.symm (413 : Fin 1024) = (179 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_413 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (179 : Fin 1024))]
  exact hs

#print axioms w2_leaf_179
theorem w2_leaf_180 : w2 180 = 0 := by
  have hpos : order.symm (428 : Fin 1024) = (180 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_428 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (180 : Fin 1024))]
  exact hs

#print axioms w2_leaf_180
theorem w2_leaf_181 : w2 181 = 0 := by
  have hpos : order.symm (429 : Fin 1024) = (181 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_429 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (181 : Fin 1024))]
  exact hs

#print axioms w2_leaf_181
theorem w2_leaf_182 : w2 182 = 0 := by
  have hpos : order.symm (444 : Fin 1024) = (182 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_444 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (182 : Fin 1024))]
  exact hs

#print axioms w2_leaf_182
theorem w2_leaf_183 : w2 183 = 0 := by
  have hpos : order.symm (445 : Fin 1024) = (183 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_445 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (183 : Fin 1024))]
  exact hs

#print axioms w2_leaf_183
theorem w2_leaf_184 : w2 184 = 0 := by
  have hpos : order.symm (460 : Fin 1024) = (184 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_460 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (184 : Fin 1024))]
  exact hs

#print axioms w2_leaf_184
theorem w2_leaf_185 : w2 185 = 0 := by
  have hpos : order.symm (461 : Fin 1024) = (185 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_461 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (185 : Fin 1024))]
  exact hs

#print axioms w2_leaf_185
theorem w2_leaf_186 : w2 186 = 0 := by
  have hpos : order.symm (476 : Fin 1024) = (186 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_476 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (186 : Fin 1024))]
  exact hs

#print axioms w2_leaf_186
theorem w2_leaf_187 : w2 187 = 0 := by
  have hpos : order.symm (477 : Fin 1024) = (187 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_477 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (187 : Fin 1024))]
  exact hs

#print axioms w2_leaf_187
theorem w2_leaf_188 : w2 188 = 0 := by
  have hpos : order.symm (492 : Fin 1024) = (188 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_492 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (188 : Fin 1024))]
  exact hs

#print axioms w2_leaf_188
theorem w2_leaf_189 : w2 189 = 0 := by
  have hpos : order.symm (493 : Fin 1024) = (189 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_493 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (189 : Fin 1024))]
  exact hs

#print axioms w2_leaf_189
theorem w2_leaf_190 : w2 190 = 0 := by
  have hpos : order.symm (508 : Fin 1024) = (190 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_508 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (190 : Fin 1024))]
  exact hs

#print axioms w2_leaf_190
theorem w2_leaf_191 : w2 191 = 0 := by
  have hpos : order.symm (509 : Fin 1024) = (191 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_509 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (191 : Fin 1024))]
  exact hs

#print axioms w2_leaf_191
theorem w2_leaf_192 : w2 192 = 0 := by
  have hpos : order.symm (524 : Fin 1024) = (192 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_524 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (192 : Fin 1024))]
  exact hs

#print axioms w2_leaf_192
theorem w2_leaf_193 : w2 193 = 0 := by
  have hpos : order.symm (525 : Fin 1024) = (193 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_525 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (193 : Fin 1024))]
  exact hs

#print axioms w2_leaf_193
theorem w2_leaf_194 : w2 194 = 0 := by
  have hpos : order.symm (540 : Fin 1024) = (194 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_540 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (194 : Fin 1024))]
  exact hs

#print axioms w2_leaf_194
theorem w2_leaf_195 : w2 195 = 0 := by
  have hpos : order.symm (541 : Fin 1024) = (195 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_541 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (195 : Fin 1024))]
  exact hs

#print axioms w2_leaf_195
theorem w2_leaf_196 : w2 196 = 0 := by
  have hpos : order.symm (556 : Fin 1024) = (196 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_556 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (196 : Fin 1024))]
  exact hs

#print axioms w2_leaf_196
theorem w2_leaf_197 : w2 197 = 0 := by
  have hpos : order.symm (557 : Fin 1024) = (197 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_557 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (197 : Fin 1024))]
  exact hs

#print axioms w2_leaf_197
theorem w2_leaf_198 : w2 198 = 0 := by
  have hpos : order.symm (572 : Fin 1024) = (198 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_572 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (198 : Fin 1024))]
  exact hs

#print axioms w2_leaf_198
theorem w2_leaf_199 : w2 199 = 0 := by
  have hpos : order.symm (573 : Fin 1024) = (199 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_573 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (199 : Fin 1024))]
  exact hs

#print axioms w2_leaf_199
theorem w2_leaf_200 : w2 200 = 0 := by
  have hpos : order.symm (588 : Fin 1024) = (200 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_588 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (200 : Fin 1024))]
  exact hs

#print axioms w2_leaf_200
theorem w2_leaf_201 : w2 201 = 0 := by
  have hpos : order.symm (589 : Fin 1024) = (201 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_589 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (201 : Fin 1024))]
  exact hs

#print axioms w2_leaf_201
theorem w2_leaf_202 : w2 202 = 0 := by
  have hpos : order.symm (604 : Fin 1024) = (202 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_604 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (202 : Fin 1024))]
  exact hs

#print axioms w2_leaf_202
theorem w2_leaf_203 : w2 203 = 0 := by
  have hpos : order.symm (605 : Fin 1024) = (203 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_605 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (203 : Fin 1024))]
  exact hs

#print axioms w2_leaf_203
theorem w2_leaf_204 : w2 204 = 0 := by
  have hpos : order.symm (620 : Fin 1024) = (204 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_620 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (204 : Fin 1024))]
  exact hs

#print axioms w2_leaf_204
theorem w2_leaf_205 : w2 205 = 0 := by
  have hpos : order.symm (621 : Fin 1024) = (205 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_621 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (205 : Fin 1024))]
  exact hs

#print axioms w2_leaf_205
theorem w2_leaf_206 : w2 206 = 0 := by
  have hpos : order.symm (636 : Fin 1024) = (206 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_636 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (206 : Fin 1024))]
  exact hs

#print axioms w2_leaf_206
theorem w2_leaf_207 : w2 207 = 0 := by
  have hpos : order.symm (637 : Fin 1024) = (207 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_637 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (207 : Fin 1024))]
  exact hs

#print axioms w2_leaf_207
theorem w2_leaf_208 : w2 208 = 0 := by
  have hpos : order.symm (652 : Fin 1024) = (208 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_652 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (208 : Fin 1024))]
  exact hs

#print axioms w2_leaf_208
theorem w2_leaf_209 : w2 209 = 0 := by
  have hpos : order.symm (653 : Fin 1024) = (209 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_653 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (209 : Fin 1024))]
  exact hs

#print axioms w2_leaf_209
theorem w2_leaf_210 : w2 210 = 0 := by
  have hpos : order.symm (668 : Fin 1024) = (210 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_668 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (210 : Fin 1024))]
  exact hs

#print axioms w2_leaf_210
theorem w2_leaf_211 : w2 211 = 0 := by
  have hpos : order.symm (669 : Fin 1024) = (211 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_669 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (211 : Fin 1024))]
  exact hs

#print axioms w2_leaf_211
theorem w2_leaf_212 : w2 212 = 0 := by
  have hpos : order.symm (684 : Fin 1024) = (212 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_684 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (212 : Fin 1024))]
  exact hs

#print axioms w2_leaf_212
theorem w2_leaf_213 : w2 213 = 0 := by
  have hpos : order.symm (685 : Fin 1024) = (213 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_685 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (213 : Fin 1024))]
  exact hs

#print axioms w2_leaf_213
theorem w2_leaf_214 : w2 214 = 0 := by
  have hpos : order.symm (700 : Fin 1024) = (214 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_700 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (214 : Fin 1024))]
  exact hs

#print axioms w2_leaf_214
theorem w2_leaf_215 : w2 215 = 0 := by
  have hpos : order.symm (701 : Fin 1024) = (215 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_701 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (215 : Fin 1024))]
  exact hs

#print axioms w2_leaf_215
theorem w2_leaf_216 : w2 216 = 0 := by
  have hpos : order.symm (716 : Fin 1024) = (216 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_716 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (216 : Fin 1024))]
  exact hs

#print axioms w2_leaf_216
theorem w2_leaf_217 : w2 217 = 0 := by
  have hpos : order.symm (717 : Fin 1024) = (217 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_717 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (217 : Fin 1024))]
  exact hs

#print axioms w2_leaf_217
theorem w2_leaf_218 : w2 218 = 0 := by
  have hpos : order.symm (732 : Fin 1024) = (218 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_732 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (218 : Fin 1024))]
  exact hs

#print axioms w2_leaf_218
theorem w2_leaf_219 : w2 219 = 0 := by
  have hpos : order.symm (733 : Fin 1024) = (219 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_733 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (219 : Fin 1024))]
  exact hs

#print axioms w2_leaf_219
theorem w2_leaf_220 : w2 220 = 0 := by
  have hpos : order.symm (748 : Fin 1024) = (220 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_748 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (220 : Fin 1024))]
  exact hs

#print axioms w2_leaf_220
theorem w2_leaf_221 : w2 221 = 0 := by
  have hpos : order.symm (749 : Fin 1024) = (221 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_749 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (221 : Fin 1024))]
  exact hs

#print axioms w2_leaf_221
theorem w2_leaf_222 : w2 222 = 0 := by
  have hpos : order.symm (764 : Fin 1024) = (222 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_764 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (222 : Fin 1024))]
  exact hs

#print axioms w2_leaf_222
theorem w2_leaf_223 : w2 223 = 0 := by
  have hpos : order.symm (765 : Fin 1024) = (223 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_765 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (223 : Fin 1024))]
  exact hs

#print axioms w2_leaf_223
theorem w2_leaf_224 : w2 224 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (780 : Fin 1024) = (224 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeaves.point2_candidate780_transport_exact (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (224 : Fin 1024))]
  exact hs

#print axioms w2_leaf_224
theorem w2_leaf_225 : w2 225 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (781 : Fin 1024) = (225 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_781 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (225 : Fin 1024))]
  exact hs

#print axioms w2_leaf_225
theorem w2_leaf_226 : w2 226 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (796 : Fin 1024) = (226 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_796 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (226 : Fin 1024))]
  exact hs

#print axioms w2_leaf_226
theorem w2_leaf_227 : w2 227 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (797 : Fin 1024) = (227 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_797 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (227 : Fin 1024))]
  exact hs

#print axioms w2_leaf_227
theorem w2_leaf_228 : w2 228 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (812 : Fin 1024) = (228 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_812 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (228 : Fin 1024))]
  exact hs

#print axioms w2_leaf_228
theorem w2_leaf_229 : w2 229 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (813 : Fin 1024) = (229 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_813 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (229 : Fin 1024))]
  exact hs

#print axioms w2_leaf_229
theorem w2_leaf_230 : w2 230 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (828 : Fin 1024) = (230 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_828 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (230 : Fin 1024))]
  exact hs

#print axioms w2_leaf_230
theorem w2_leaf_231 : w2 231 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (829 : Fin 1024) = (231 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_829 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (231 : Fin 1024))]
  exact hs

#print axioms w2_leaf_231
theorem w2_leaf_232 : w2 232 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (844 : Fin 1024) = (232 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_844 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (232 : Fin 1024))]
  exact hs

#print axioms w2_leaf_232
theorem w2_leaf_233 : w2 233 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (845 : Fin 1024) = (233 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_845 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (233 : Fin 1024))]
  exact hs

#print axioms w2_leaf_233
theorem w2_leaf_234 : w2 234 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (860 : Fin 1024) = (234 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_860 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (234 : Fin 1024))]
  exact hs

#print axioms w2_leaf_234
theorem w2_leaf_235 : w2 235 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (861 : Fin 1024) = (235 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_861 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (235 : Fin 1024))]
  exact hs

#print axioms w2_leaf_235
theorem w2_leaf_236 : w2 236 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (876 : Fin 1024) = (236 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_876 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (236 : Fin 1024))]
  exact hs

#print axioms w2_leaf_236
theorem w2_leaf_237 : w2 237 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (877 : Fin 1024) = (237 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_877 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (237 : Fin 1024))]
  exact hs

#print axioms w2_leaf_237
theorem w2_leaf_238 : w2 238 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (892 : Fin 1024) = (238 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_892 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (238 : Fin 1024))]
  exact hs

#print axioms w2_leaf_238
theorem w2_leaf_239 : w2 239 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (893 : Fin 1024) = (239 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_893 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (239 : Fin 1024))]
  exact hs

#print axioms w2_leaf_239
theorem w2_leaf_240 : w2 240 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (908 : Fin 1024) = (240 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_908 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (240 : Fin 1024))]
  exact hs

#print axioms w2_leaf_240
theorem w2_leaf_241 : w2 241 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (909 : Fin 1024) = (241 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_909 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (241 : Fin 1024))]
  exact hs

#print axioms w2_leaf_241
theorem w2_leaf_242 : w2 242 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (924 : Fin 1024) = (242 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_924 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (242 : Fin 1024))]
  exact hs

#print axioms w2_leaf_242
theorem w2_leaf_243 : w2 243 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (925 : Fin 1024) = (243 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_925 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (243 : Fin 1024))]
  exact hs

#print axioms w2_leaf_243
theorem w2_leaf_244 : w2 244 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (940 : Fin 1024) = (244 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_940 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (244 : Fin 1024))]
  exact hs

#print axioms w2_leaf_244
theorem w2_leaf_245 : w2 245 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (941 : Fin 1024) = (245 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_941 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (245 : Fin 1024))]
  exact hs

#print axioms w2_leaf_245
theorem w2_leaf_246 : w2 246 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (956 : Fin 1024) = (246 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_956 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (246 : Fin 1024))]
  exact hs

#print axioms w2_leaf_246
theorem w2_leaf_247 : w2 247 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (957 : Fin 1024) = (247 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_957 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (247 : Fin 1024))]
  exact hs

#print axioms w2_leaf_247
theorem w2_leaf_248 : w2 248 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (972 : Fin 1024) = (248 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_972 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (248 : Fin 1024))]
  exact hs

#print axioms w2_leaf_248
theorem w2_leaf_249 : w2 249 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (973 : Fin 1024) = (249 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_973 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (249 : Fin 1024))]
  exact hs

#print axioms w2_leaf_249
theorem w2_leaf_250 : w2 250 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (988 : Fin 1024) = (250 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_988 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (250 : Fin 1024))]
  exact hs

#print axioms w2_leaf_250
theorem w2_leaf_251 : w2 251 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (989 : Fin 1024) = (251 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_989 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (251 : Fin 1024))]
  exact hs

#print axioms w2_leaf_251
theorem w2_leaf_252 : w2 252 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (1004 : Fin 1024) = (252 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_1004 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (252 : Fin 1024))]
  exact hs

#print axioms w2_leaf_252
theorem w2_leaf_253 : w2 253 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (1005 : Fin 1024) = (253 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1005 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (253 : Fin 1024))]
  exact hs

#print axioms w2_leaf_253
theorem w2_leaf_254 : w2 254 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (1020 : Fin 1024) = (254 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_1020 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (254 : Fin 1024))]
  exact hs

#print axioms w2_leaf_254
theorem w2_leaf_255 : w2 255 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (1021 : Fin 1024) = (255 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_1021 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (255 : Fin 1024))]
  exact hs

#print axioms w2_leaf_255
theorem w2_leaf_256 : w2 256 = 0 := by
  have hpos : order.symm (10 : Fin 1024) = (256 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_10 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (256 : Fin 1024))]
  exact hs

#print axioms w2_leaf_256
theorem w2_leaf_257 : w2 257 = 0 := by
  have hpos : order.symm (11 : Fin 1024) = (257 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_11 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (257 : Fin 1024))]
  exact hs

#print axioms w2_leaf_257
theorem w2_leaf_258 : w2 258 = 0 := by
  have hpos : order.symm (26 : Fin 1024) = (258 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_26 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (258 : Fin 1024))]
  exact hs

#print axioms w2_leaf_258
theorem w2_leaf_259 : w2 259 = 0 := by
  have hpos : order.symm (27 : Fin 1024) = (259 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_27 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (259 : Fin 1024))]
  exact hs

#print axioms w2_leaf_259
theorem w2_leaf_260 : w2 260 = 0 := by
  have hpos : order.symm (42 : Fin 1024) = (260 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_42 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (260 : Fin 1024))]
  exact hs

#print axioms w2_leaf_260
theorem w2_leaf_261 : w2 261 = 0 := by
  have hpos : order.symm (43 : Fin 1024) = (261 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_43 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (261 : Fin 1024))]
  exact hs

#print axioms w2_leaf_261
theorem w2_leaf_262 : w2 262 = 0 := by
  have hpos : order.symm (58 : Fin 1024) = (262 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_58 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (262 : Fin 1024))]
  exact hs

#print axioms w2_leaf_262
theorem w2_leaf_263 : w2 263 = 0 := by
  have hpos : order.symm (59 : Fin 1024) = (263 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_59 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (263 : Fin 1024))]
  exact hs

#print axioms w2_leaf_263
theorem w2_leaf_264 : w2 264 = 0 := by
  have hpos : order.symm (74 : Fin 1024) = (264 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_74 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (264 : Fin 1024))]
  exact hs

#print axioms w2_leaf_264
theorem w2_leaf_265 : w2 265 = 0 := by
  have hpos : order.symm (75 : Fin 1024) = (265 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_75 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (265 : Fin 1024))]
  exact hs

#print axioms w2_leaf_265
theorem w2_leaf_266 : w2 266 = 0 := by
  have hpos : order.symm (90 : Fin 1024) = (266 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_90 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (266 : Fin 1024))]
  exact hs

#print axioms w2_leaf_266
theorem w2_leaf_267 : w2 267 = 0 := by
  have hpos : order.symm (91 : Fin 1024) = (267 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_91 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (267 : Fin 1024))]
  exact hs

#print axioms w2_leaf_267
theorem w2_leaf_268 : w2 268 = 0 := by
  have hpos : order.symm (106 : Fin 1024) = (268 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_106 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (268 : Fin 1024))]
  exact hs

#print axioms w2_leaf_268
theorem w2_leaf_269 : w2 269 = 0 := by
  have hpos : order.symm (107 : Fin 1024) = (269 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_107 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (269 : Fin 1024))]
  exact hs

#print axioms w2_leaf_269
theorem w2_leaf_270 : w2 270 = 0 := by
  have hpos : order.symm (122 : Fin 1024) = (270 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_122 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (270 : Fin 1024))]
  exact hs

#print axioms w2_leaf_270
theorem w2_leaf_271 : w2 271 = 0 := by
  have hpos : order.symm (123 : Fin 1024) = (271 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_123 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (271 : Fin 1024))]
  exact hs

#print axioms w2_leaf_271
theorem w2_leaf_272 : w2 272 = 0 := by
  have hpos : order.symm (138 : Fin 1024) = (272 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_138 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (272 : Fin 1024))]
  exact hs

#print axioms w2_leaf_272
theorem w2_leaf_273 : w2 273 = 0 := by
  have hpos : order.symm (139 : Fin 1024) = (273 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_139 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (273 : Fin 1024))]
  exact hs

#print axioms w2_leaf_273
theorem w2_leaf_274 : w2 274 = 0 := by
  have hpos : order.symm (154 : Fin 1024) = (274 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_154 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (274 : Fin 1024))]
  exact hs

#print axioms w2_leaf_274
theorem w2_leaf_275 : w2 275 = 0 := by
  have hpos : order.symm (155 : Fin 1024) = (275 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_155 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (275 : Fin 1024))]
  exact hs

#print axioms w2_leaf_275
theorem w2_leaf_276 : w2 276 = 0 := by
  have hpos : order.symm (170 : Fin 1024) = (276 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_170 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (276 : Fin 1024))]
  exact hs

#print axioms w2_leaf_276
theorem w2_leaf_277 : w2 277 = 0 := by
  have hpos : order.symm (171 : Fin 1024) = (277 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_171 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (277 : Fin 1024))]
  exact hs

#print axioms w2_leaf_277
theorem w2_leaf_278 : w2 278 = 0 := by
  have hpos : order.symm (186 : Fin 1024) = (278 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_186 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (278 : Fin 1024))]
  exact hs

#print axioms w2_leaf_278
theorem w2_leaf_279 : w2 279 = 0 := by
  have hpos : order.symm (187 : Fin 1024) = (279 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_187 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (279 : Fin 1024))]
  exact hs

#print axioms w2_leaf_279
theorem w2_leaf_280 : w2 280 = 0 := by
  have hpos : order.symm (202 : Fin 1024) = (280 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_202 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (280 : Fin 1024))]
  exact hs

#print axioms w2_leaf_280
theorem w2_leaf_281 : w2 281 = 0 := by
  have hpos : order.symm (203 : Fin 1024) = (281 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_203 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (281 : Fin 1024))]
  exact hs

#print axioms w2_leaf_281
theorem w2_leaf_282 : w2 282 = 0 := by
  have hpos : order.symm (218 : Fin 1024) = (282 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_218 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (282 : Fin 1024))]
  exact hs

#print axioms w2_leaf_282
theorem w2_leaf_283 : w2 283 = 0 := by
  have hpos : order.symm (219 : Fin 1024) = (283 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_219 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (283 : Fin 1024))]
  exact hs

#print axioms w2_leaf_283
theorem w2_leaf_284 : w2 284 = 0 := by
  have hpos : order.symm (234 : Fin 1024) = (284 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_234 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (284 : Fin 1024))]
  exact hs

#print axioms w2_leaf_284
theorem w2_leaf_285 : w2 285 = 0 := by
  have hpos : order.symm (235 : Fin 1024) = (285 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_235 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (285 : Fin 1024))]
  exact hs

#print axioms w2_leaf_285
theorem w2_leaf_286 : w2 286 = 0 := by
  have hpos : order.symm (250 : Fin 1024) = (286 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_250 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (286 : Fin 1024))]
  exact hs

#print axioms w2_leaf_286
theorem w2_leaf_287 : w2 287 = 0 := by
  have hpos : order.symm (251 : Fin 1024) = (287 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_251 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (287 : Fin 1024))]
  exact hs

#print axioms w2_leaf_287
theorem w2_leaf_288 : w2 288 = 0 := by
  have hpos : order.symm (266 : Fin 1024) = (288 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_266 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (288 : Fin 1024))]
  exact hs

#print axioms w2_leaf_288
theorem w2_leaf_289 : w2 289 = 0 := by
  have hpos : order.symm (267 : Fin 1024) = (289 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_267 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (289 : Fin 1024))]
  exact hs

#print axioms w2_leaf_289
theorem w2_leaf_290 : w2 290 = 0 := by
  have hpos : order.symm (282 : Fin 1024) = (290 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_282 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (290 : Fin 1024))]
  exact hs

#print axioms w2_leaf_290
theorem w2_leaf_291 : w2 291 = 0 := by
  have hpos : order.symm (283 : Fin 1024) = (291 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_283 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (291 : Fin 1024))]
  exact hs

#print axioms w2_leaf_291
theorem w2_leaf_292 : w2 292 = 0 := by
  have hpos : order.symm (298 : Fin 1024) = (292 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_298 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (292 : Fin 1024))]
  exact hs

#print axioms w2_leaf_292
theorem w2_leaf_293 : w2 293 = 0 := by
  have hpos : order.symm (299 : Fin 1024) = (293 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_299 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (293 : Fin 1024))]
  exact hs

#print axioms w2_leaf_293
theorem w2_leaf_294 : w2 294 = 0 := by
  have hpos : order.symm (314 : Fin 1024) = (294 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_314 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (294 : Fin 1024))]
  exact hs

#print axioms w2_leaf_294
theorem w2_leaf_295 : w2 295 = 0 := by
  have hpos : order.symm (315 : Fin 1024) = (295 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_315 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (295 : Fin 1024))]
  exact hs

#print axioms w2_leaf_295
theorem w2_leaf_296 : w2 296 = 0 := by
  have hpos : order.symm (330 : Fin 1024) = (296 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_330 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (296 : Fin 1024))]
  exact hs

#print axioms w2_leaf_296
theorem w2_leaf_297 : w2 297 = 0 := by
  have hpos : order.symm (331 : Fin 1024) = (297 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_331 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (297 : Fin 1024))]
  exact hs

#print axioms w2_leaf_297
theorem w2_leaf_298 : w2 298 = 0 := by
  have hpos : order.symm (346 : Fin 1024) = (298 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_346 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (298 : Fin 1024))]
  exact hs

#print axioms w2_leaf_298
theorem w2_leaf_299 : w2 299 = 0 := by
  have hpos : order.symm (347 : Fin 1024) = (299 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_347 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (299 : Fin 1024))]
  exact hs

#print axioms w2_leaf_299
theorem w2_leaf_300 : w2 300 = 0 := by
  have hpos : order.symm (362 : Fin 1024) = (300 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_362 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (300 : Fin 1024))]
  exact hs

#print axioms w2_leaf_300
theorem w2_leaf_301 : w2 301 = 0 := by
  have hpos : order.symm (363 : Fin 1024) = (301 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_363 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (301 : Fin 1024))]
  exact hs

#print axioms w2_leaf_301
theorem w2_leaf_302 : w2 302 = 0 := by
  have hpos : order.symm (378 : Fin 1024) = (302 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_378 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (302 : Fin 1024))]
  exact hs

#print axioms w2_leaf_302
theorem w2_leaf_303 : w2 303 = 0 := by
  have hpos : order.symm (379 : Fin 1024) = (303 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_379 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (303 : Fin 1024))]
  exact hs

#print axioms w2_leaf_303
theorem w2_leaf_304 : w2 304 = 0 := by
  have hpos : order.symm (394 : Fin 1024) = (304 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_394 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (304 : Fin 1024))]
  exact hs

#print axioms w2_leaf_304
theorem w2_leaf_305 : w2 305 = 0 := by
  have hpos : order.symm (395 : Fin 1024) = (305 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_395 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (305 : Fin 1024))]
  exact hs

#print axioms w2_leaf_305
theorem w2_leaf_306 : w2 306 = 0 := by
  have hpos : order.symm (410 : Fin 1024) = (306 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_410 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (306 : Fin 1024))]
  exact hs

#print axioms w2_leaf_306
theorem w2_leaf_307 : w2 307 = 0 := by
  have hpos : order.symm (411 : Fin 1024) = (307 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_411 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (307 : Fin 1024))]
  exact hs

#print axioms w2_leaf_307
theorem w2_leaf_308 : w2 308 = 0 := by
  have hpos : order.symm (426 : Fin 1024) = (308 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_426 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (308 : Fin 1024))]
  exact hs

#print axioms w2_leaf_308
theorem w2_leaf_309 : w2 309 = 0 := by
  have hpos : order.symm (427 : Fin 1024) = (309 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_427 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (309 : Fin 1024))]
  exact hs

#print axioms w2_leaf_309
theorem w2_leaf_310 : w2 310 = 0 := by
  have hpos : order.symm (442 : Fin 1024) = (310 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_442 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (310 : Fin 1024))]
  exact hs

#print axioms w2_leaf_310
theorem w2_leaf_311 : w2 311 = 0 := by
  have hpos : order.symm (443 : Fin 1024) = (311 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_443 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (311 : Fin 1024))]
  exact hs

#print axioms w2_leaf_311
theorem w2_leaf_312 : w2 312 = 0 := by
  have hpos : order.symm (458 : Fin 1024) = (312 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_458 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (312 : Fin 1024))]
  exact hs

#print axioms w2_leaf_312
theorem w2_leaf_313 : w2 313 = 0 := by
  have hpos : order.symm (459 : Fin 1024) = (313 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_459 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (313 : Fin 1024))]
  exact hs

#print axioms w2_leaf_313
theorem w2_leaf_314 : w2 314 = 0 := by
  have hpos : order.symm (474 : Fin 1024) = (314 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_474 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (314 : Fin 1024))]
  exact hs

#print axioms w2_leaf_314
theorem w2_leaf_315 : w2 315 = 0 := by
  have hpos : order.symm (475 : Fin 1024) = (315 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_475 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (315 : Fin 1024))]
  exact hs

#print axioms w2_leaf_315
theorem w2_leaf_316 : w2 316 = 0 := by
  have hpos : order.symm (490 : Fin 1024) = (316 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_490 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (316 : Fin 1024))]
  exact hs

#print axioms w2_leaf_316
theorem w2_leaf_317 : w2 317 = 0 := by
  have hpos : order.symm (491 : Fin 1024) = (317 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_491 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (317 : Fin 1024))]
  exact hs

#print axioms w2_leaf_317
theorem w2_leaf_318 : w2 318 = 0 := by
  have hpos : order.symm (506 : Fin 1024) = (318 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_506 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (318 : Fin 1024))]
  exact hs

#print axioms w2_leaf_318
theorem w2_leaf_319 : w2 319 = 0 := by
  have hpos : order.symm (507 : Fin 1024) = (319 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_507 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (319 : Fin 1024))]
  exact hs

#print axioms w2_leaf_319
theorem w2_leaf_320 : w2 320 = 0 := by
  have hpos : order.symm (522 : Fin 1024) = (320 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_522 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (320 : Fin 1024))]
  exact hs

#print axioms w2_leaf_320
theorem w2_leaf_321 : w2 321 = 0 := by
  have hpos : order.symm (523 : Fin 1024) = (321 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_523 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (321 : Fin 1024))]
  exact hs

#print axioms w2_leaf_321
theorem w2_leaf_322 : w2 322 = 0 := by
  have hpos : order.symm (538 : Fin 1024) = (322 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_538 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (322 : Fin 1024))]
  exact hs

#print axioms w2_leaf_322
theorem w2_leaf_323 : w2 323 = 0 := by
  have hpos : order.symm (539 : Fin 1024) = (323 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_539 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (323 : Fin 1024))]
  exact hs

#print axioms w2_leaf_323
theorem w2_leaf_324 : w2 324 = 0 := by
  have hpos : order.symm (554 : Fin 1024) = (324 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_554 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (324 : Fin 1024))]
  exact hs

#print axioms w2_leaf_324
theorem w2_leaf_325 : w2 325 = 0 := by
  have hpos : order.symm (555 : Fin 1024) = (325 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_555 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (325 : Fin 1024))]
  exact hs

#print axioms w2_leaf_325
theorem w2_leaf_326 : w2 326 = 0 := by
  have hpos : order.symm (570 : Fin 1024) = (326 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_570 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (326 : Fin 1024))]
  exact hs

#print axioms w2_leaf_326
theorem w2_leaf_327 : w2 327 = 0 := by
  have hpos : order.symm (571 : Fin 1024) = (327 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_571 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (327 : Fin 1024))]
  exact hs

#print axioms w2_leaf_327
theorem w2_leaf_328 : w2 328 = 0 := by
  have hpos : order.symm (586 : Fin 1024) = (328 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_586 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (328 : Fin 1024))]
  exact hs

#print axioms w2_leaf_328
theorem w2_leaf_329 : w2 329 = 0 := by
  have hpos : order.symm (587 : Fin 1024) = (329 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_587 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (329 : Fin 1024))]
  exact hs

#print axioms w2_leaf_329
theorem w2_leaf_330 : w2 330 = 0 := by
  have hpos : order.symm (602 : Fin 1024) = (330 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_602 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (330 : Fin 1024))]
  exact hs

#print axioms w2_leaf_330
theorem w2_leaf_331 : w2 331 = 0 := by
  have hpos : order.symm (603 : Fin 1024) = (331 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_603 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (331 : Fin 1024))]
  exact hs

#print axioms w2_leaf_331
theorem w2_leaf_332 : w2 332 = 0 := by
  have hpos : order.symm (618 : Fin 1024) = (332 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_618 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (332 : Fin 1024))]
  exact hs

#print axioms w2_leaf_332
theorem w2_leaf_333 : w2 333 = 0 := by
  have hpos : order.symm (619 : Fin 1024) = (333 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_619 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (333 : Fin 1024))]
  exact hs

#print axioms w2_leaf_333
theorem w2_leaf_334 : w2 334 = 0 := by
  have hpos : order.symm (634 : Fin 1024) = (334 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_634 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (334 : Fin 1024))]
  exact hs

#print axioms w2_leaf_334
theorem w2_leaf_335 : w2 335 = 0 := by
  have hpos : order.symm (635 : Fin 1024) = (335 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_635 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (335 : Fin 1024))]
  exact hs

#print axioms w2_leaf_335
theorem w2_leaf_336 : w2 336 = 0 := by
  have hpos : order.symm (650 : Fin 1024) = (336 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_650 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (336 : Fin 1024))]
  exact hs

#print axioms w2_leaf_336
theorem w2_leaf_337 : w2 337 = 0 := by
  have hpos : order.symm (651 : Fin 1024) = (337 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_651 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (337 : Fin 1024))]
  exact hs

#print axioms w2_leaf_337
theorem w2_leaf_338 : w2 338 = 0 := by
  have hpos : order.symm (666 : Fin 1024) = (338 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_666 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (338 : Fin 1024))]
  exact hs

#print axioms w2_leaf_338
theorem w2_leaf_339 : w2 339 = 0 := by
  have hpos : order.symm (667 : Fin 1024) = (339 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_667 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (339 : Fin 1024))]
  exact hs

#print axioms w2_leaf_339
theorem w2_leaf_340 : w2 340 = 0 := by
  have hpos : order.symm (682 : Fin 1024) = (340 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_682 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (340 : Fin 1024))]
  exact hs

#print axioms w2_leaf_340
theorem w2_leaf_341 : w2 341 = 0 := by
  have hpos : order.symm (683 : Fin 1024) = (341 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_683 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (341 : Fin 1024))]
  exact hs

#print axioms w2_leaf_341
theorem w2_leaf_342 : w2 342 = 0 := by
  have hpos : order.symm (698 : Fin 1024) = (342 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_698 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (342 : Fin 1024))]
  exact hs

#print axioms w2_leaf_342
theorem w2_leaf_343 : w2 343 = 0 := by
  have hpos : order.symm (699 : Fin 1024) = (343 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_699 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (343 : Fin 1024))]
  exact hs

#print axioms w2_leaf_343
theorem w2_leaf_344 : w2 344 = 0 := by
  have hpos : order.symm (714 : Fin 1024) = (344 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_714 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (344 : Fin 1024))]
  exact hs

#print axioms w2_leaf_344
theorem w2_leaf_345 : w2 345 = 0 := by
  have hpos : order.symm (715 : Fin 1024) = (345 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_715 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (345 : Fin 1024))]
  exact hs

#print axioms w2_leaf_345
theorem w2_leaf_346 : w2 346 = 0 := by
  have hpos : order.symm (730 : Fin 1024) = (346 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_730 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (346 : Fin 1024))]
  exact hs

#print axioms w2_leaf_346
theorem w2_leaf_347 : w2 347 = 0 := by
  have hpos : order.symm (731 : Fin 1024) = (347 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_731 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (347 : Fin 1024))]
  exact hs

#print axioms w2_leaf_347
theorem w2_leaf_348 : w2 348 = 0 := by
  have hpos : order.symm (746 : Fin 1024) = (348 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_746 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (348 : Fin 1024))]
  exact hs

#print axioms w2_leaf_348
theorem w2_leaf_349 : w2 349 = 0 := by
  have hpos : order.symm (747 : Fin 1024) = (349 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_747 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (349 : Fin 1024))]
  exact hs

#print axioms w2_leaf_349
theorem w2_leaf_350 : w2 350 = 0 := by
  have hpos : order.symm (762 : Fin 1024) = (350 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_762 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (350 : Fin 1024))]
  exact hs

#print axioms w2_leaf_350
theorem w2_leaf_351 : w2 351 = 0 := by
  have hpos : order.symm (763 : Fin 1024) = (351 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_763 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (351 : Fin 1024))]
  exact hs

#print axioms w2_leaf_351
theorem w2_leaf_352 : w2 352 = 0 := by
  have hpos : order.symm (778 : Fin 1024) = (352 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_778 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (352 : Fin 1024))]
  exact hs

#print axioms w2_leaf_352
theorem w2_leaf_353 : w2 353 = 0 := by
  have hpos : order.symm (779 : Fin 1024) = (353 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_779 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (353 : Fin 1024))]
  exact hs

#print axioms w2_leaf_353
theorem w2_leaf_354 : w2 354 = 0 := by
  have hpos : order.symm (794 : Fin 1024) = (354 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_794 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (354 : Fin 1024))]
  exact hs

#print axioms w2_leaf_354
theorem w2_leaf_355 : w2 355 = 0 := by
  have hpos : order.symm (795 : Fin 1024) = (355 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_795 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (355 : Fin 1024))]
  exact hs

#print axioms w2_leaf_355
theorem w2_leaf_356 : w2 356 = 0 := by
  have hpos : order.symm (810 : Fin 1024) = (356 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_810 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (356 : Fin 1024))]
  exact hs

#print axioms w2_leaf_356
theorem w2_leaf_357 : w2 357 = 0 := by
  have hpos : order.symm (811 : Fin 1024) = (357 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_811 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (357 : Fin 1024))]
  exact hs

#print axioms w2_leaf_357
theorem w2_leaf_358 : w2 358 = 0 := by
  have hpos : order.symm (826 : Fin 1024) = (358 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_826 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (358 : Fin 1024))]
  exact hs

#print axioms w2_leaf_358
theorem w2_leaf_359 : w2 359 = 0 := by
  have hpos : order.symm (827 : Fin 1024) = (359 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_827 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (359 : Fin 1024))]
  exact hs

#print axioms w2_leaf_359
theorem w2_leaf_360 : w2 360 = 0 := by
  have hpos : order.symm (842 : Fin 1024) = (360 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_842 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (360 : Fin 1024))]
  exact hs

#print axioms w2_leaf_360
theorem w2_leaf_361 : w2 361 = 0 := by
  have hpos : order.symm (843 : Fin 1024) = (361 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_843 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (361 : Fin 1024))]
  exact hs

#print axioms w2_leaf_361
theorem w2_leaf_362 : w2 362 = 0 := by
  have hpos : order.symm (858 : Fin 1024) = (362 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_858 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (362 : Fin 1024))]
  exact hs

#print axioms w2_leaf_362
theorem w2_leaf_363 : w2 363 = 0 := by
  have hpos : order.symm (859 : Fin 1024) = (363 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_859 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (363 : Fin 1024))]
  exact hs

#print axioms w2_leaf_363
theorem w2_leaf_364 : w2 364 = 0 := by
  have hpos : order.symm (874 : Fin 1024) = (364 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_874 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (364 : Fin 1024))]
  exact hs

#print axioms w2_leaf_364
theorem w2_leaf_365 : w2 365 = 0 := by
  have hpos : order.symm (875 : Fin 1024) = (365 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_875 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (365 : Fin 1024))]
  exact hs

#print axioms w2_leaf_365
theorem w2_leaf_366 : w2 366 = 0 := by
  have hpos : order.symm (890 : Fin 1024) = (366 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_890 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (366 : Fin 1024))]
  exact hs

#print axioms w2_leaf_366
theorem w2_leaf_367 : w2 367 = 0 := by
  have hpos : order.symm (891 : Fin 1024) = (367 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_891 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (367 : Fin 1024))]
  exact hs

#print axioms w2_leaf_367
theorem w2_leaf_368 : w2 368 = 0 := by
  have hpos : order.symm (906 : Fin 1024) = (368 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_906 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (368 : Fin 1024))]
  exact hs

#print axioms w2_leaf_368
theorem w2_leaf_369 : w2 369 = 0 := by
  have hpos : order.symm (907 : Fin 1024) = (369 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_907 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (369 : Fin 1024))]
  exact hs

#print axioms w2_leaf_369
theorem w2_leaf_370 : w2 370 = 0 := by
  have hpos : order.symm (922 : Fin 1024) = (370 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_922 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (370 : Fin 1024))]
  exact hs

#print axioms w2_leaf_370
theorem w2_leaf_371 : w2 371 = 0 := by
  have hpos : order.symm (923 : Fin 1024) = (371 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_923 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (371 : Fin 1024))]
  exact hs

#print axioms w2_leaf_371
theorem w2_leaf_372 : w2 372 = 0 := by
  have hpos : order.symm (938 : Fin 1024) = (372 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_938 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (372 : Fin 1024))]
  exact hs

#print axioms w2_leaf_372
theorem w2_leaf_373 : w2 373 = 0 := by
  have hpos : order.symm (939 : Fin 1024) = (373 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_939 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (373 : Fin 1024))]
  exact hs

#print axioms w2_leaf_373
theorem w2_leaf_374 : w2 374 = 0 := by
  have hpos : order.symm (954 : Fin 1024) = (374 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_954 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (374 : Fin 1024))]
  exact hs

#print axioms w2_leaf_374
theorem w2_leaf_375 : w2 375 = 0 := by
  have hpos : order.symm (955 : Fin 1024) = (375 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_955 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (375 : Fin 1024))]
  exact hs

#print axioms w2_leaf_375
theorem w2_leaf_376 : w2 376 = 0 := by
  have hpos : order.symm (970 : Fin 1024) = (376 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_970 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (376 : Fin 1024))]
  exact hs

#print axioms w2_leaf_376
theorem w2_leaf_377 : w2 377 = 0 := by
  have hpos : order.symm (971 : Fin 1024) = (377 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_971 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (377 : Fin 1024))]
  exact hs

#print axioms w2_leaf_377
theorem w2_leaf_378 : w2 378 = 0 := by
  have hpos : order.symm (986 : Fin 1024) = (378 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_986 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (378 : Fin 1024))]
  exact hs

#print axioms w2_leaf_378
theorem w2_leaf_379 : w2 379 = 0 := by
  have hpos : order.symm (987 : Fin 1024) = (379 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_987 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (379 : Fin 1024))]
  exact hs

#print axioms w2_leaf_379
theorem w2_leaf_380 : w2 380 = 0 := by
  have hpos : order.symm (1002 : Fin 1024) = (380 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1002 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (380 : Fin 1024))]
  exact hs

#print axioms w2_leaf_380
theorem w2_leaf_381 : w2 381 = 0 := by
  have hpos : order.symm (1003 : Fin 1024) = (381 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_1003 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (381 : Fin 1024))]
  exact hs

#print axioms w2_leaf_381
theorem w2_leaf_382 : w2 382 = 0 := by
  have hpos : order.symm (1018 : Fin 1024) = (382 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1018 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (382 : Fin 1024))]
  exact hs

#print axioms w2_leaf_382
theorem w2_leaf_383 : w2 383 = 0 := by
  have hpos : order.symm (1019 : Fin 1024) = (383 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_1019 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (383 : Fin 1024))]
  exact hs

#print axioms w2_leaf_383
theorem w2_leaf_384 : w2 384 = 0 := by
  have hpos : order.symm (8 : Fin 1024) = (384 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_8 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (384 : Fin 1024))]
  exact hs

#print axioms w2_leaf_384
theorem w2_leaf_385 : w2 385 = 0 := by
  have hpos : order.symm (9 : Fin 1024) = (385 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_9 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (385 : Fin 1024))]
  exact hs

#print axioms w2_leaf_385
theorem w2_leaf_386 : w2 386 = 0 := by
  have hpos : order.symm (24 : Fin 1024) = (386 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_24 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (386 : Fin 1024))]
  exact hs

#print axioms w2_leaf_386
theorem w2_leaf_448 : w2 448 = 0 := by
  have hpos : order.symm (520 : Fin 1024) = (448 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_520 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (448 : Fin 1024))]
  exact hs

#print axioms w2_leaf_448
theorem w2_leaf_449 : w2 449 = 0 := by
  have hpos : order.symm (521 : Fin 1024) = (449 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_521 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (449 : Fin 1024))]
  exact hs

#print axioms w2_leaf_449
theorem w2_leaf_450 : w2 450 = 0 := by
  have hpos : order.symm (536 : Fin 1024) = (450 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_536 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (450 : Fin 1024))]
  exact hs

#print axioms w2_leaf_450
theorem w2_leaf_480 : w2 480 = ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (776 : Fin 1024) = (480 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_776 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (480 : Fin 1024))]
  exact hs

#print axioms w2_leaf_480
theorem w2_leaf_481 : w2 481 = ([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (777 : Fin 1024) = (481 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_777 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (481 : Fin 1024))]
  exact hs

#print axioms w2_leaf_481
theorem w2_leaf_482 : w2 482 = ([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (792 : Fin 1024) = (482 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_792 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (482 : Fin 1024))]
  exact hs

#print axioms w2_leaf_482
theorem w2_leaf_496 : w2 496 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (904 : Fin 1024) = (496 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_904 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (496 : Fin 1024))]
  exact hs

#print axioms w2_leaf_496
theorem w2_leaf_497 : w2 497 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (905 : Fin 1024) = (497 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_905 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (497 : Fin 1024))]
  exact hs

#print axioms w2_leaf_497
theorem w2_leaf_498 : w2 498 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (920 : Fin 1024) = (498 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_920 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (498 : Fin 1024))]
  exact hs

#print axioms w2_leaf_498
theorem w2_leaf_499 : w2 499 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (921 : Fin 1024) = (499 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_921 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (499 : Fin 1024))]
  exact hs

#print axioms w2_leaf_499
theorem w2_leaf_500 : w2 500 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (936 : Fin 1024) = (500 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_936 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (500 : Fin 1024))]
  exact hs

#print axioms w2_leaf_500
theorem w2_leaf_501 : w2 501 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (937 : Fin 1024) = (501 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_937 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (501 : Fin 1024))]
  exact hs

#print axioms w2_leaf_501
theorem w2_leaf_502 : w2 502 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (952 : Fin 1024) = (502 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_952 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (502 : Fin 1024))]
  exact hs

#print axioms w2_leaf_502
theorem w2_leaf_503 : w2 503 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (953 : Fin 1024) = (503 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_953 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (503 : Fin 1024))]
  exact hs

#print axioms w2_leaf_503
theorem w2_leaf_504 : w2 504 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (968 : Fin 1024) = (504 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_968 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (504 : Fin 1024))]
  exact hs

#print axioms w2_leaf_504
theorem w2_leaf_505 : w2 505 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (969 : Fin 1024) = (505 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_969 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (505 : Fin 1024))]
  exact hs

#print axioms w2_leaf_505
theorem w2_leaf_506 : w2 506 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (984 : Fin 1024) = (506 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_984 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (506 : Fin 1024))]
  exact hs

#print axioms w2_leaf_506
theorem w2_leaf_507 : w2 507 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (985 : Fin 1024) = (507 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_985 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (507 : Fin 1024))]
  exact hs

#print axioms w2_leaf_507
theorem w2_leaf_508 : w2 508 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (1000 : Fin 1024) = (508 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_1000 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (508 : Fin 1024))]
  exact hs

#print axioms w2_leaf_508
theorem w2_leaf_509 : w2 509 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (1001 : Fin 1024) = (509 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1001 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (509 : Fin 1024))]
  exact hs

#print axioms w2_leaf_509
theorem w2_leaf_510 : w2 510 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (1016 : Fin 1024) = (510 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_1016 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (510 : Fin 1024))]
  exact hs

#print axioms w2_leaf_510
theorem w2_leaf_511 : w2 511 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (1017 : Fin 1024) = (511 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1017 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (511 : Fin 1024))]
  exact hs

#print axioms w2_leaf_511
theorem w2_leaf_512 : w2 512 = 0 := by
  have hpos : order.symm (6 : Fin 1024) = (512 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_6 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (512 : Fin 1024))]
  exact hs

#print axioms w2_leaf_512
theorem w2_leaf_513 : w2 513 = 0 := by
  have hpos : order.symm (7 : Fin 1024) = (513 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_7 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (513 : Fin 1024))]
  exact hs

#print axioms w2_leaf_513
theorem w2_leaf_514 : w2 514 = 0 := by
  have hpos : order.symm (22 : Fin 1024) = (514 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_22 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (514 : Fin 1024))]
  exact hs

#print axioms w2_leaf_514
theorem w2_leaf_576 : w2 576 = 0 := by
  have hpos : order.symm (518 : Fin 1024) = (576 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_518 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (576 : Fin 1024))]
  exact hs

#print axioms w2_leaf_576
theorem w2_leaf_577 : w2 577 = 0 := by
  have hpos : order.symm (519 : Fin 1024) = (577 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_519 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (577 : Fin 1024))]
  exact hs

#print axioms w2_leaf_577
theorem w2_leaf_578 : w2 578 = 0 := by
  have hpos : order.symm (534 : Fin 1024) = (578 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_534 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (578 : Fin 1024))]
  exact hs

#print axioms w2_leaf_578
theorem w2_leaf_608 : w2 608 = 0 := by
  have hpos : order.symm (774 : Fin 1024) = (608 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_774 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (608 : Fin 1024))]
  exact hs

#print axioms w2_leaf_608
theorem w2_leaf_609 : w2 609 = 0 := by
  have hpos : order.symm (775 : Fin 1024) = (609 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_775 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (609 : Fin 1024))]
  exact hs

#print axioms w2_leaf_609
theorem w2_leaf_610 : w2 610 = 0 := by
  have hpos : order.symm (790 : Fin 1024) = (610 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_790 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (610 : Fin 1024))]
  exact hs

#print axioms w2_leaf_610
theorem w2_leaf_624 : w2 624 = 0 := by
  have hpos : order.symm (902 : Fin 1024) = (624 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_902 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (624 : Fin 1024))]
  exact hs

#print axioms w2_leaf_624
theorem w2_leaf_625 : w2 625 = 0 := by
  have hpos : order.symm (903 : Fin 1024) = (625 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_903 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (625 : Fin 1024))]
  exact hs

#print axioms w2_leaf_625
theorem w2_leaf_626 : w2 626 = 0 := by
  have hpos : order.symm (918 : Fin 1024) = (626 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_918 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (626 : Fin 1024))]
  exact hs

#print axioms w2_leaf_626
theorem w2_leaf_627 : w2 627 = 0 := by
  have hpos : order.symm (919 : Fin 1024) = (627 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_919 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (627 : Fin 1024))]
  exact hs

#print axioms w2_leaf_627
theorem w2_leaf_628 : w2 628 = 0 := by
  have hpos : order.symm (934 : Fin 1024) = (628 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_934 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (628 : Fin 1024))]
  exact hs

#print axioms w2_leaf_628
theorem w2_leaf_629 : w2 629 = 0 := by
  have hpos : order.symm (935 : Fin 1024) = (629 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_935 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (629 : Fin 1024))]
  exact hs

#print axioms w2_leaf_629
theorem w2_leaf_630 : w2 630 = 0 := by
  have hpos : order.symm (950 : Fin 1024) = (630 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_950 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (630 : Fin 1024))]
  exact hs

#print axioms w2_leaf_630
theorem w2_leaf_631 : w2 631 = 0 := by
  have hpos : order.symm (951 : Fin 1024) = (631 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_951 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (631 : Fin 1024))]
  exact hs

#print axioms w2_leaf_631
theorem w2_leaf_632 : w2 632 = 0 := by
  have hpos : order.symm (966 : Fin 1024) = (632 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_966 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (632 : Fin 1024))]
  exact hs

#print axioms w2_leaf_632
theorem w2_leaf_633 : w2 633 = 0 := by
  have hpos : order.symm (967 : Fin 1024) = (633 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_967 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (633 : Fin 1024))]
  exact hs

#print axioms w2_leaf_633
theorem w2_leaf_634 : w2 634 = 0 := by
  have hpos : order.symm (982 : Fin 1024) = (634 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_982 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (634 : Fin 1024))]
  exact hs

#print axioms w2_leaf_634
theorem w2_leaf_635 : w2 635 = 0 := by
  have hpos : order.symm (983 : Fin 1024) = (635 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_983 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (635 : Fin 1024))]
  exact hs

#print axioms w2_leaf_635
theorem w2_leaf_636 : w2 636 = 0 := by
  have hpos : order.symm (998 : Fin 1024) = (636 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_998 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (636 : Fin 1024))]
  exact hs

#print axioms w2_leaf_636
theorem w2_leaf_637 : w2 637 = 0 := by
  have hpos : order.symm (999 : Fin 1024) = (637 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_999 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (637 : Fin 1024))]
  exact hs

#print axioms w2_leaf_637
theorem w2_leaf_638 : w2 638 = 0 := by
  have hpos : order.symm (1014 : Fin 1024) = (638 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1014 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (638 : Fin 1024))]
  exact hs

#print axioms w2_leaf_638
theorem w2_leaf_639 : w2 639 = 0 := by
  have hpos : order.symm (1015 : Fin 1024) = (639 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1015 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (639 : Fin 1024))]
  exact hs

#print axioms w2_leaf_639
theorem w2_leaf_640 : w2 640 = 0 := by
  have hpos : order.symm (4 : Fin 1024) = (640 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_4 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (640 : Fin 1024))]
  exact hs

#print axioms w2_leaf_640
theorem w2_leaf_641 : w2 641 = 0 := by
  have hpos : order.symm (5 : Fin 1024) = (641 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_5 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (641 : Fin 1024))]
  exact hs

#print axioms w2_leaf_641
theorem w2_leaf_642 : w2 642 = 0 := by
  have hpos : order.symm (20 : Fin 1024) = (642 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_20 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (642 : Fin 1024))]
  exact hs

#print axioms w2_leaf_642
theorem w2_leaf_704 : w2 704 = 0 := by
  have hpos : order.symm (516 : Fin 1024) = (704 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_516 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (704 : Fin 1024))]
  exact hs

#print axioms w2_leaf_704
theorem w2_leaf_736 : w2 736 = ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (772 : Fin 1024) = (736 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_772 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (736 : Fin 1024))]
  exact hs

#print axioms w2_leaf_736
theorem w2_leaf_752 : w2 752 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (900 : Fin 1024) = (752 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_900 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (752 : Fin 1024))]
  exact hs

#print axioms w2_leaf_752
theorem w2_leaf_753 : w2 753 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (901 : Fin 1024) = (753 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_901 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (753 : Fin 1024))]
  exact hs

#print axioms w2_leaf_753
theorem w2_leaf_754 : w2 754 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (916 : Fin 1024) = (754 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_916 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (754 : Fin 1024))]
  exact hs

#print axioms w2_leaf_754
theorem w2_leaf_755 : w2 755 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (917 : Fin 1024) = (755 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_917 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (755 : Fin 1024))]
  exact hs

#print axioms w2_leaf_755
theorem w2_leaf_756 : w2 756 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (932 : Fin 1024) = (756 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_932 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (756 : Fin 1024))]
  exact hs

#print axioms w2_leaf_756
theorem w2_leaf_757 : w2 757 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (933 : Fin 1024) = (757 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_933 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (757 : Fin 1024))]
  exact hs

#print axioms w2_leaf_757
theorem w2_leaf_758 : w2 758 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (948 : Fin 1024) = (758 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_948 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (758 : Fin 1024))]
  exact hs

#print axioms w2_leaf_758
theorem w2_leaf_759 : w2 759 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (949 : Fin 1024) = (759 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_949 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (759 : Fin 1024))]
  exact hs

#print axioms w2_leaf_759
theorem w2_leaf_760 : w2 760 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (964 : Fin 1024) = (760 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_964 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (760 : Fin 1024))]
  exact hs

#print axioms w2_leaf_760
theorem w2_leaf_761 : w2 761 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (965 : Fin 1024) = (761 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_965 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (761 : Fin 1024))]
  exact hs

#print axioms w2_leaf_761
theorem w2_leaf_762 : w2 762 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (980 : Fin 1024) = (762 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_980 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (762 : Fin 1024))]
  exact hs

#print axioms w2_leaf_762
theorem w2_leaf_763 : w2 763 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (981 : Fin 1024) = (763 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_981 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (763 : Fin 1024))]
  exact hs

#print axioms w2_leaf_763
theorem w2_leaf_764 : w2 764 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (996 : Fin 1024) = (764 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_996 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (764 : Fin 1024))]
  exact hs

#print axioms w2_leaf_764
theorem w2_leaf_765 : w2 765 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (997 : Fin 1024) = (765 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_997 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (765 : Fin 1024))]
  exact hs

#print axioms w2_leaf_765
theorem w2_leaf_766 : w2 766 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hpos : order.symm (1012 : Fin 1024) = (766 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1012 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (766 : Fin 1024))]
  exact hs

#print axioms w2_leaf_766
theorem w2_leaf_767 : w2 767 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hpos : order.symm (1013 : Fin 1024) = (767 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_1013 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (767 : Fin 1024))]
  exact hs

#print axioms w2_leaf_767
theorem w2_leaf_768 : w2 768 = 0 := by
  have hpos : order.symm (2 : Fin 1024) = (768 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_2 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (768 : Fin 1024))]
  exact hs

#print axioms w2_leaf_768
theorem w2_leaf_832 : w2 832 = 0 := by
  have hpos : order.symm (514 : Fin 1024) = (832 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_514 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (832 : Fin 1024))]
  exact hs

#print axioms w2_leaf_832
theorem w2_leaf_864 : w2 864 = 0 := by
  have hpos : order.symm (770 : Fin 1024) = (864 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_770 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (864 : Fin 1024))]
  exact hs

#print axioms w2_leaf_864
theorem w2_leaf_880 : w2 880 = 0 := by
  have hpos : order.symm (898 : Fin 1024) = (880 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_898 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (880 : Fin 1024))]
  exact hs

#print axioms w2_leaf_880
theorem w2_leaf_881 : w2 881 = 0 := by
  have hpos : order.symm (899 : Fin 1024) = (881 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_899 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (881 : Fin 1024))]
  exact hs

#print axioms w2_leaf_881
theorem w2_leaf_882 : w2 882 = 0 := by
  have hpos : order.symm (914 : Fin 1024) = (882 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_914 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (882 : Fin 1024))]
  exact hs

#print axioms w2_leaf_882
theorem w2_leaf_883 : w2 883 = 0 := by
  have hpos : order.symm (915 : Fin 1024) = (883 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_915 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (883 : Fin 1024))]
  exact hs

#print axioms w2_leaf_883
theorem w2_leaf_884 : w2 884 = 0 := by
  have hpos : order.symm (930 : Fin 1024) = (884 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_930 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (884 : Fin 1024))]
  exact hs

#print axioms w2_leaf_884
theorem w2_leaf_885 : w2 885 = 0 := by
  have hpos : order.symm (931 : Fin 1024) = (885 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_931 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (885 : Fin 1024))]
  exact hs

#print axioms w2_leaf_885
theorem w2_leaf_886 : w2 886 = 0 := by
  have hpos : order.symm (946 : Fin 1024) = (886 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_946 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (886 : Fin 1024))]
  exact hs

#print axioms w2_leaf_886
theorem w2_leaf_887 : w2 887 = 0 := by
  have hpos : order.symm (947 : Fin 1024) = (887 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_947 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (887 : Fin 1024))]
  exact hs

#print axioms w2_leaf_887
theorem w2_leaf_888 : w2 888 = 0 := by
  have hpos : order.symm (962 : Fin 1024) = (888 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_962 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (888 : Fin 1024))]
  exact hs

#print axioms w2_leaf_888
theorem w2_leaf_889 : w2 889 = 0 := by
  have hpos : order.symm (963 : Fin 1024) = (889 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_963 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (889 : Fin 1024))]
  exact hs

#print axioms w2_leaf_889
theorem w2_leaf_890 : w2 890 = 0 := by
  have hpos : order.symm (978 : Fin 1024) = (890 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_978 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (890 : Fin 1024))]
  exact hs

#print axioms w2_leaf_890
theorem w2_leaf_891 : w2 891 = 0 := by
  have hpos : order.symm (979 : Fin 1024) = (891 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_979 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (891 : Fin 1024))]
  exact hs

#print axioms w2_leaf_891
theorem w2_leaf_892 : w2 892 = 0 := by
  have hpos : order.symm (994 : Fin 1024) = (892 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_994 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (892 : Fin 1024))]
  exact hs

#print axioms w2_leaf_892
theorem w2_leaf_893 : w2 893 = 0 := by
  have hpos : order.symm (995 : Fin 1024) = (893 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_995 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (893 : Fin 1024))]
  exact hs

#print axioms w2_leaf_893
theorem w2_leaf_894 : w2 894 = 0 := by
  have hpos : order.symm (1010 : Fin 1024) = (894 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_1010 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (894 : Fin 1024))]
  exact hs

#print axioms w2_leaf_894
theorem w2_leaf_895 : w2 895 = 0 := by
  have hpos : order.symm (1011 : Fin 1024) = (895 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_1011 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (895 : Fin 1024))]
  exact hs

#print axioms w2_leaf_895
theorem w2_leaf_896 : w2 896 = 0 := by
  have hpos : order.symm (0 : Fin 1024) = (896 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_0 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (896 : Fin 1024))]
  exact hs

#print axioms w2_leaf_896
theorem w2_leaf_900 : w2 900 = 0 := by
  have hpos : order.symm (32 : Fin 1024) = (900 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_32 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (900 : Fin 1024))]
  exact hs

#print axioms w2_leaf_900
theorem w2_leaf_901 : w2 901 = 0 := by
  have hpos : order.symm (33 : Fin 1024) = (901 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_33 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (901 : Fin 1024))]
  exact hs

#print axioms w2_leaf_901
theorem w2_leaf_902 : w2 902 = 0 := by
  have hpos : order.symm (48 : Fin 1024) = (902 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_48 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (902 : Fin 1024))]
  exact hs

#print axioms w2_leaf_902
theorem w2_leaf_903 : w2 903 = 0 := by
  have hpos : order.symm (49 : Fin 1024) = (903 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_49 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (903 : Fin 1024))]
  exact hs

#print axioms w2_leaf_903
theorem w2_leaf_904 : w2 904 = 0 := by
  have hpos : order.symm (64 : Fin 1024) = (904 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_64 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (904 : Fin 1024))]
  exact hs

#print axioms w2_leaf_904
theorem w2_leaf_905 : w2 905 = 0 := by
  have hpos : order.symm (65 : Fin 1024) = (905 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_65 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (905 : Fin 1024))]
  exact hs

#print axioms w2_leaf_905
theorem w2_leaf_906 : w2 906 = 0 := by
  have hpos : order.symm (80 : Fin 1024) = (906 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_80 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (906 : Fin 1024))]
  exact hs

#print axioms w2_leaf_906
theorem w2_leaf_907 : w2 907 = 0 := by
  have hpos : order.symm (81 : Fin 1024) = (907 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_81 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (907 : Fin 1024))]
  exact hs

#print axioms w2_leaf_907
theorem w2_leaf_908 : w2 908 = 0 := by
  have hpos : order.symm (96 : Fin 1024) = (908 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_96 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (908 : Fin 1024))]
  exact hs

#print axioms w2_leaf_908
theorem w2_leaf_909 : w2 909 = 0 := by
  have hpos : order.symm (97 : Fin 1024) = (909 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_97 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (909 : Fin 1024))]
  exact hs

#print axioms w2_leaf_909
theorem w2_leaf_910 : w2 910 = 0 := by
  have hpos : order.symm (112 : Fin 1024) = (910 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_112 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (910 : Fin 1024))]
  exact hs

#print axioms w2_leaf_910
theorem w2_leaf_911 : w2 911 = 0 := by
  have hpos : order.symm (113 : Fin 1024) = (911 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_113 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (911 : Fin 1024))]
  exact hs

#print axioms w2_leaf_911
theorem w2_leaf_912 : w2 912 = 0 := by
  have hpos : order.symm (128 : Fin 1024) = (912 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_128 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (912 : Fin 1024))]
  exact hs

#print axioms w2_leaf_912
theorem w2_leaf_913 : w2 913 = 0 := by
  have hpos : order.symm (129 : Fin 1024) = (913 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_129 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (913 : Fin 1024))]
  exact hs

#print axioms w2_leaf_913
theorem w2_leaf_914 : w2 914 = 0 := by
  have hpos : order.symm (144 : Fin 1024) = (914 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_144 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (914 : Fin 1024))]
  exact hs

#print axioms w2_leaf_914
theorem w2_leaf_915 : w2 915 = 0 := by
  have hpos : order.symm (145 : Fin 1024) = (915 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_145 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (915 : Fin 1024))]
  exact hs

#print axioms w2_leaf_915
theorem w2_leaf_916 : w2 916 = 0 := by
  have hpos : order.symm (160 : Fin 1024) = (916 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_160 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (916 : Fin 1024))]
  exact hs

#print axioms w2_leaf_916
theorem w2_leaf_917 : w2 917 = 0 := by
  have hpos : order.symm (161 : Fin 1024) = (917 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_161 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (917 : Fin 1024))]
  exact hs

#print axioms w2_leaf_917
theorem w2_leaf_918 : w2 918 = 0 := by
  have hpos : order.symm (176 : Fin 1024) = (918 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_176 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (918 : Fin 1024))]
  exact hs

#print axioms w2_leaf_918
theorem w2_leaf_919 : w2 919 = 0 := by
  have hpos : order.symm (177 : Fin 1024) = (919 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_177 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (919 : Fin 1024))]
  exact hs

#print axioms w2_leaf_919
theorem w2_leaf_920 : w2 920 = 0 := by
  have hpos : order.symm (192 : Fin 1024) = (920 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_192 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (920 : Fin 1024))]
  exact hs

#print axioms w2_leaf_920
theorem w2_leaf_921 : w2 921 = 0 := by
  have hpos : order.symm (193 : Fin 1024) = (921 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_193 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (921 : Fin 1024))]
  exact hs

#print axioms w2_leaf_921
theorem w2_leaf_922 : w2 922 = 0 := by
  have hpos : order.symm (208 : Fin 1024) = (922 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_208 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (922 : Fin 1024))]
  exact hs

#print axioms w2_leaf_922
theorem w2_leaf_923 : w2 923 = 0 := by
  have hpos : order.symm (209 : Fin 1024) = (923 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_209 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (923 : Fin 1024))]
  exact hs

#print axioms w2_leaf_923
theorem w2_leaf_924 : w2 924 = 0 := by
  have hpos : order.symm (224 : Fin 1024) = (924 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_224 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (924 : Fin 1024))]
  exact hs

#print axioms w2_leaf_924
theorem w2_leaf_925 : w2 925 = 0 := by
  have hpos : order.symm (225 : Fin 1024) = (925 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_225 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (925 : Fin 1024))]
  exact hs

#print axioms w2_leaf_925
theorem w2_leaf_926 : w2 926 = 0 := by
  have hpos : order.symm (240 : Fin 1024) = (926 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_240 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (926 : Fin 1024))]
  exact hs

#print axioms w2_leaf_926
theorem w2_leaf_927 : w2 927 = 0 := by
  have hpos : order.symm (241 : Fin 1024) = (927 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_241 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (927 : Fin 1024))]
  exact hs

#print axioms w2_leaf_927
theorem w2_leaf_928 : w2 928 = 0 := by
  have hpos : order.symm (256 : Fin 1024) = (928 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_256 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (928 : Fin 1024))]
  exact hs

#print axioms w2_leaf_928
theorem w2_leaf_929 : w2 929 = 0 := by
  have hpos : order.symm (257 : Fin 1024) = (929 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_257 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (929 : Fin 1024))]
  exact hs

#print axioms w2_leaf_929
theorem w2_leaf_930 : w2 930 = 0 := by
  have hpos : order.symm (272 : Fin 1024) = (930 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_272 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (930 : Fin 1024))]
  exact hs

#print axioms w2_leaf_930
theorem w2_leaf_931 : w2 931 = 0 := by
  have hpos : order.symm (273 : Fin 1024) = (931 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_273 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (931 : Fin 1024))]
  exact hs

#print axioms w2_leaf_931
theorem w2_leaf_932 : w2 932 = 0 := by
  have hpos : order.symm (288 : Fin 1024) = (932 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_288 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (932 : Fin 1024))]
  exact hs

#print axioms w2_leaf_932
theorem w2_leaf_933 : w2 933 = 0 := by
  have hpos : order.symm (289 : Fin 1024) = (933 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_289 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (933 : Fin 1024))]
  exact hs

#print axioms w2_leaf_933
theorem w2_leaf_934 : w2 934 = 0 := by
  have hpos : order.symm (304 : Fin 1024) = (934 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_304 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (934 : Fin 1024))]
  exact hs

#print axioms w2_leaf_934
theorem w2_leaf_935 : w2 935 = 0 := by
  have hpos : order.symm (305 : Fin 1024) = (935 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_305 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (935 : Fin 1024))]
  exact hs

#print axioms w2_leaf_935
theorem w2_leaf_936 : w2 936 = 0 := by
  have hpos : order.symm (320 : Fin 1024) = (936 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_320 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (936 : Fin 1024))]
  exact hs

#print axioms w2_leaf_936
theorem w2_leaf_937 : w2 937 = 0 := by
  have hpos : order.symm (321 : Fin 1024) = (937 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_321 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (937 : Fin 1024))]
  exact hs

#print axioms w2_leaf_937
theorem w2_leaf_938 : w2 938 = 0 := by
  have hpos : order.symm (336 : Fin 1024) = (938 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_336 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (938 : Fin 1024))]
  exact hs

#print axioms w2_leaf_938
theorem w2_leaf_939 : w2 939 = 0 := by
  have hpos : order.symm (337 : Fin 1024) = (939 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_337 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (939 : Fin 1024))]
  exact hs

#print axioms w2_leaf_939
theorem w2_leaf_940 : w2 940 = 0 := by
  have hpos : order.symm (352 : Fin 1024) = (940 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_352 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (940 : Fin 1024))]
  exact hs

#print axioms w2_leaf_940
theorem w2_leaf_941 : w2 941 = 0 := by
  have hpos : order.symm (353 : Fin 1024) = (941 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_353 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (941 : Fin 1024))]
  exact hs

#print axioms w2_leaf_941
theorem w2_leaf_942 : w2 942 = 0 := by
  have hpos : order.symm (368 : Fin 1024) = (942 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_368 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (942 : Fin 1024))]
  exact hs

#print axioms w2_leaf_942
theorem w2_leaf_943 : w2 943 = 0 := by
  have hpos : order.symm (369 : Fin 1024) = (943 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_369 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (943 : Fin 1024))]
  exact hs

#print axioms w2_leaf_943
theorem w2_leaf_944 : w2 944 = 0 := by
  have hpos : order.symm (384 : Fin 1024) = (944 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_384 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (944 : Fin 1024))]
  exact hs

#print axioms w2_leaf_944
theorem w2_leaf_945 : w2 945 = 0 := by
  have hpos : order.symm (385 : Fin 1024) = (945 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_385 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (945 : Fin 1024))]
  exact hs

#print axioms w2_leaf_945
theorem w2_leaf_946 : w2 946 = 0 := by
  have hpos : order.symm (400 : Fin 1024) = (946 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_400 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (946 : Fin 1024))]
  exact hs

#print axioms w2_leaf_946
theorem w2_leaf_947 : w2 947 = 0 := by
  have hpos : order.symm (401 : Fin 1024) = (947 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_401 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (947 : Fin 1024))]
  exact hs

#print axioms w2_leaf_947
theorem w2_leaf_948 : w2 948 = 0 := by
  have hpos : order.symm (416 : Fin 1024) = (948 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_416 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (948 : Fin 1024))]
  exact hs

#print axioms w2_leaf_948
theorem w2_leaf_949 : w2 949 = 0 := by
  have hpos : order.symm (417 : Fin 1024) = (949 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_417 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (949 : Fin 1024))]
  exact hs

#print axioms w2_leaf_949
theorem w2_leaf_950 : w2 950 = 0 := by
  have hpos : order.symm (432 : Fin 1024) = (950 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_432 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (950 : Fin 1024))]
  exact hs

#print axioms w2_leaf_950
theorem w2_leaf_951 : w2 951 = 0 := by
  have hpos : order.symm (433 : Fin 1024) = (951 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_433 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (951 : Fin 1024))]
  exact hs

#print axioms w2_leaf_951
theorem w2_leaf_952 : w2 952 = 0 := by
  have hpos : order.symm (448 : Fin 1024) = (952 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_448 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (952 : Fin 1024))]
  exact hs

#print axioms w2_leaf_952
theorem w2_leaf_953 : w2 953 = 0 := by
  have hpos : order.symm (449 : Fin 1024) = (953 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_449 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (953 : Fin 1024))]
  exact hs

#print axioms w2_leaf_953
theorem w2_leaf_954 : w2 954 = 0 := by
  have hpos : order.symm (464 : Fin 1024) = (954 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_464 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (954 : Fin 1024))]
  exact hs

#print axioms w2_leaf_954
theorem w2_leaf_955 : w2 955 = 0 := by
  have hpos : order.symm (465 : Fin 1024) = (955 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_465 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (955 : Fin 1024))]
  exact hs

#print axioms w2_leaf_955
theorem w2_leaf_956 : w2 956 = 0 := by
  have hpos : order.symm (480 : Fin 1024) = (956 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_480 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (956 : Fin 1024))]
  exact hs

#print axioms w2_leaf_956
theorem w2_leaf_957 : w2 957 = 0 := by
  have hpos : order.symm (481 : Fin 1024) = (957 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_481 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (957 : Fin 1024))]
  exact hs

#print axioms w2_leaf_957
theorem w2_leaf_958 : w2 958 = 0 := by
  have hpos : order.symm (496 : Fin 1024) = (958 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_496 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (958 : Fin 1024))]
  exact hs

#print axioms w2_leaf_958
theorem w2_leaf_959 : w2 959 = 0 := by
  have hpos : order.symm (497 : Fin 1024) = (959 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_497 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (959 : Fin 1024))]
  exact hs

#print axioms w2_leaf_959
theorem w2_leaf_960 : w2 960 = 0 := by
  have hpos : order.symm (512 : Fin 1024) = (960 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_512 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (960 : Fin 1024))]
  exact hs

#print axioms w2_leaf_960
theorem w2_leaf_961 : w2 961 = 0 := by
  have hpos : order.symm (513 : Fin 1024) = (961 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_513 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (961 : Fin 1024))]
  exact hs

#print axioms w2_leaf_961
theorem w2_leaf_962 : w2 962 = 0 := by
  have hpos : order.symm (528 : Fin 1024) = (962 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_528 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (962 : Fin 1024))]
  exact hs

#print axioms w2_leaf_962
theorem w2_leaf_963 : w2 963 = 0 := by
  have hpos : order.symm (529 : Fin 1024) = (963 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_529 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (963 : Fin 1024))]
  exact hs

#print axioms w2_leaf_963
theorem w2_leaf_964 : w2 964 = 0 := by
  have hpos : order.symm (544 : Fin 1024) = (964 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_544 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (964 : Fin 1024))]
  exact hs

#print axioms w2_leaf_964
theorem w2_leaf_965 : w2 965 = 0 := by
  have hpos : order.symm (545 : Fin 1024) = (965 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_545 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (965 : Fin 1024))]
  exact hs

#print axioms w2_leaf_965
theorem w2_leaf_966 : w2 966 = 0 := by
  have hpos : order.symm (560 : Fin 1024) = (966 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_560 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (966 : Fin 1024))]
  exact hs

#print axioms w2_leaf_966
theorem w2_leaf_967 : w2 967 = 0 := by
  have hpos : order.symm (561 : Fin 1024) = (967 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_561 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (967 : Fin 1024))]
  exact hs

#print axioms w2_leaf_967
theorem w2_leaf_968 : w2 968 = 0 := by
  have hpos : order.symm (576 : Fin 1024) = (968 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_576 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (968 : Fin 1024))]
  exact hs

#print axioms w2_leaf_968
theorem w2_leaf_969 : w2 969 = 0 := by
  have hpos : order.symm (577 : Fin 1024) = (969 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_577 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (969 : Fin 1024))]
  exact hs

#print axioms w2_leaf_969
theorem w2_leaf_970 : w2 970 = 0 := by
  have hpos : order.symm (592 : Fin 1024) = (970 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_592 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (970 : Fin 1024))]
  exact hs

#print axioms w2_leaf_970
theorem w2_leaf_971 : w2 971 = 0 := by
  have hpos : order.symm (593 : Fin 1024) = (971 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_593 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (971 : Fin 1024))]
  exact hs

#print axioms w2_leaf_971
theorem w2_leaf_972 : w2 972 = 0 := by
  have hpos : order.symm (608 : Fin 1024) = (972 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_608 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (972 : Fin 1024))]
  exact hs

#print axioms w2_leaf_972
theorem w2_leaf_973 : w2 973 = 0 := by
  have hpos : order.symm (609 : Fin 1024) = (973 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_609 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (973 : Fin 1024))]
  exact hs

#print axioms w2_leaf_973
theorem w2_leaf_974 : w2 974 = 0 := by
  have hpos : order.symm (624 : Fin 1024) = (974 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_624 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (974 : Fin 1024))]
  exact hs

#print axioms w2_leaf_974
theorem w2_leaf_975 : w2 975 = 0 := by
  have hpos : order.symm (625 : Fin 1024) = (975 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_625 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (975 : Fin 1024))]
  exact hs

#print axioms w2_leaf_975
theorem w2_leaf_976 : w2 976 = 0 := by
  have hpos : order.symm (640 : Fin 1024) = (976 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_640 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (976 : Fin 1024))]
  exact hs

#print axioms w2_leaf_976
theorem w2_leaf_977 : w2 977 = 0 := by
  have hpos : order.symm (641 : Fin 1024) = (977 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_641 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (977 : Fin 1024))]
  exact hs

#print axioms w2_leaf_977
theorem w2_leaf_978 : w2 978 = 0 := by
  have hpos : order.symm (656 : Fin 1024) = (978 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_656 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (978 : Fin 1024))]
  exact hs

#print axioms w2_leaf_978
theorem w2_leaf_979 : w2 979 = 0 := by
  have hpos : order.symm (657 : Fin 1024) = (979 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_657 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (979 : Fin 1024))]
  exact hs

#print axioms w2_leaf_979
theorem w2_leaf_980 : w2 980 = 0 := by
  have hpos : order.symm (672 : Fin 1024) = (980 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_672 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (980 : Fin 1024))]
  exact hs

#print axioms w2_leaf_980
theorem w2_leaf_981 : w2 981 = 0 := by
  have hpos : order.symm (673 : Fin 1024) = (981 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_673 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (981 : Fin 1024))]
  exact hs

#print axioms w2_leaf_981
theorem w2_leaf_982 : w2 982 = 0 := by
  have hpos : order.symm (688 : Fin 1024) = (982 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_688 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (982 : Fin 1024))]
  exact hs

#print axioms w2_leaf_982
theorem w2_leaf_983 : w2 983 = 0 := by
  have hpos : order.symm (689 : Fin 1024) = (983 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_689 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (983 : Fin 1024))]
  exact hs

#print axioms w2_leaf_983
theorem w2_leaf_984 : w2 984 = 0 := by
  have hpos : order.symm (704 : Fin 1024) = (984 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_704 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (984 : Fin 1024))]
  exact hs

#print axioms w2_leaf_984
theorem w2_leaf_985 : w2 985 = 0 := by
  have hpos : order.symm (705 : Fin 1024) = (985 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_705 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (985 : Fin 1024))]
  exact hs

#print axioms w2_leaf_985
theorem w2_leaf_986 : w2 986 = 0 := by
  have hpos : order.symm (720 : Fin 1024) = (986 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_720 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (986 : Fin 1024))]
  exact hs

#print axioms w2_leaf_986
theorem w2_leaf_987 : w2 987 = 0 := by
  have hpos : order.symm (721 : Fin 1024) = (987 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_721 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (987 : Fin 1024))]
  exact hs

#print axioms w2_leaf_987
theorem w2_leaf_988 : w2 988 = 0 := by
  have hpos : order.symm (736 : Fin 1024) = (988 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_zero_original_736 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (988 : Fin 1024))]
  exact hs

#print axioms w2_leaf_988
theorem w2_leaf_989 : w2 989 = 0 := by
  have hpos : order.symm (737 : Fin 1024) = (989 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_737 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (989 : Fin 1024))]
  exact hs

#print axioms w2_leaf_989
theorem w2_leaf_990 : w2 990 = 0 := by
  have hpos : order.symm (752 : Fin 1024) = (990 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_zero_original_752 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (990 : Fin 1024))]
  exact hs

#print axioms w2_leaf_990
theorem w2_leaf_991 : w2 991 = 0 := by
  have hpos : order.symm (753 : Fin 1024) = (991 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_753 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (991 : Fin 1024))]
  exact hs

#print axioms w2_leaf_991
theorem w2_leaf_992 : w2 992 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (768 : Fin 1024) = (992 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_768 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (992 : Fin 1024))]
  exact hs

#print axioms w2_leaf_992
theorem w2_leaf_993 : w2 993 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (769 : Fin 1024) = (993 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_769 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (993 : Fin 1024))]
  exact hs

#print axioms w2_leaf_993
theorem w2_leaf_994 : w2 994 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (784 : Fin 1024) = (994 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_784 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (994 : Fin 1024))]
  exact hs

#print axioms w2_leaf_994
theorem w2_leaf_995 : w2 995 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (785 : Fin 1024) = (995 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_785 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (995 : Fin 1024))]
  exact hs

#print axioms w2_leaf_995
theorem w2_leaf_996 : w2 996 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (800 : Fin 1024) = (996 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_800 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (996 : Fin 1024))]
  exact hs

#print axioms w2_leaf_996
theorem w2_leaf_997 : w2 997 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (801 : Fin 1024) = (997 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_801 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (997 : Fin 1024))]
  exact hs

#print axioms w2_leaf_997
theorem w2_leaf_998 : w2 998 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (816 : Fin 1024) = (998 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_816 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (998 : Fin 1024))]
  exact hs

#print axioms w2_leaf_998
theorem w2_leaf_999 : w2 999 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (817 : Fin 1024) = (999 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_817 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (999 : Fin 1024))]
  exact hs

#print axioms w2_leaf_999
theorem w2_leaf_1000 : w2 1000 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (832 : Fin 1024) = (1000 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_832 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1000 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1000
theorem w2_leaf_1001 : w2 1001 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (833 : Fin 1024) = (1001 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_833 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1001 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1001
theorem w2_leaf_1002 : w2 1002 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (848 : Fin 1024) = (1002 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_848 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1002 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1002
theorem w2_leaf_1003 : w2 1003 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (849 : Fin 1024) = (1003 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_849 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1003 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1003
theorem w2_leaf_1004 : w2 1004 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (864 : Fin 1024) = (1004 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_864 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1004 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1004
theorem w2_leaf_1005 : w2 1005 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (865 : Fin 1024) = (1005 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_865 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1005 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1005
theorem w2_leaf_1006 : w2 1006 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (880 : Fin 1024) = (1006 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_880 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1006 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1006
theorem w2_leaf_1007 : w2 1007 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (881 : Fin 1024) = (1007 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_881 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1007 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1007
theorem w2_leaf_1008 : w2 1008 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (896 : Fin 1024) = (1008 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_896 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1008 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1008
theorem w2_leaf_1009 : w2 1009 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (897 : Fin 1024) = (1009 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_897 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1009 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1009
theorem w2_leaf_1010 : w2 1010 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (912 : Fin 1024) = (1010 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_912 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1010 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1010
theorem w2_leaf_1011 : w2 1011 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (913 : Fin 1024) = (1011 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_913 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1011 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1011
theorem w2_leaf_1012 : w2 1012 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (928 : Fin 1024) = (1012 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_928 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1012 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1012
theorem w2_leaf_1013 : w2 1013 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (929 : Fin 1024) = (1013 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_929 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1013 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1013
theorem w2_leaf_1014 : w2 1014 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (944 : Fin 1024) = (1014 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_944 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1014 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1014
theorem w2_leaf_1015 : w2 1015 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (945 : Fin 1024) = (1015 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_945 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1015 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1015
theorem w2_leaf_1016 : w2 1016 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (960 : Fin 1024) = (1016 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_960 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1016 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1016
theorem w2_leaf_1017 : w2 1017 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (961 : Fin 1024) = (1017 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_961 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1017 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1017
theorem w2_leaf_1018 : w2 1018 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (976 : Fin 1024) = (1018 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_976 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1018 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1018
theorem w2_leaf_1019 : w2 1019 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hpos : order.symm (977 : Fin 1024) = (1019 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_977 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1019 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1019
theorem w2_leaf_1020 : w2 1020 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (992 : Fin 1024) = (1020 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_992 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1020 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1020
theorem w2_leaf_1021 : w2 1021 = 0 := by
  have hpos : order.symm (1022 : Fin 1024) = (1021 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_1022 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1021 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1021
theorem w2_leaf_1022 : w2 1022 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hpos : order.symm (1008 : Fin 1024) = (1022 : Fin 1024) := by decide
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_1008 (F := M)
  rw [← hpos] at hs
  rw [w2_at (i := (1022 : Fin 1024))]
  exact hs

#print axioms w2_leaf_1022
end
end AspisV8R19.R780Point02WeightShared
