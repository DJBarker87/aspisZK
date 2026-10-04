import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk01
import AspisV8R19.R772Point02DualLeavesChunk02
import AspisV8R19.R772Point02DualLeavesChunk15
import AspisV8R19.R772Point02DualLeavesChunk16
import AspisV8R19.R772Point02DualLeavesChunk26
import AspisV8R19.R772Point02DualLeavesChunk28

namespace AspisV8R19.R780Point02WeightSharedChunk01
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_111 : order.symm (895 : Fin 1024) = (111 : Fin 1024) := by decide
#print axioms hpos_leaf_111

theorem w0_leaf_111 : w0 111 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_895 (F := M)
  rw [hpos_leaf_111] at hs
  calc w0 111 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (111 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (111 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_111

theorem w2_leaf_111 : w2 111 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_895 (F := M)
  rw [hpos_leaf_111] at hs
  calc w2 111 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (111 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (111 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_111

theorem hpos_leaf_112 : order.symm (910 : Fin 1024) = (112 : Fin 1024) := by decide
#print axioms hpos_leaf_112

theorem w0_leaf_112 : w0 112 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_910 (F := M)
  rw [hpos_leaf_112] at hs
  calc w0 112 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (112 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (112 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_112

theorem w2_leaf_112 : w2 112 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_910 (F := M)
  rw [hpos_leaf_112] at hs
  calc w2 112 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (112 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (112 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_112

theorem hpos_leaf_113 : order.symm (911 : Fin 1024) = (113 : Fin 1024) := by decide
#print axioms hpos_leaf_113

theorem w0_leaf_113 : w0 113 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_911 (F := M)
  rw [hpos_leaf_113] at hs
  calc w0 113 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (113 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (113 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_113

theorem w2_leaf_113 : w2 113 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_911 (F := M)
  rw [hpos_leaf_113] at hs
  calc w2 113 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (113 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (113 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_113

theorem hpos_leaf_114 : order.symm (926 : Fin 1024) = (114 : Fin 1024) := by decide
#print axioms hpos_leaf_114

theorem w0_leaf_114 : w0 114 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_926 (F := M)
  rw [hpos_leaf_114] at hs
  calc w0 114 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (114 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (114 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_114

theorem w2_leaf_114 : w2 114 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_926 (F := M)
  rw [hpos_leaf_114] at hs
  calc w2 114 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (114 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (114 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_114

theorem hpos_leaf_115 : order.symm (927 : Fin 1024) = (115 : Fin 1024) := by decide
#print axioms hpos_leaf_115

theorem w0_leaf_115 : w0 115 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_927 (F := M)
  rw [hpos_leaf_115] at hs
  calc w0 115 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (115 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (115 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_115

theorem w2_leaf_115 : w2 115 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_927 (F := M)
  rw [hpos_leaf_115] at hs
  calc w2 115 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (115 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (115 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_115

theorem hpos_leaf_116 : order.symm (942 : Fin 1024) = (116 : Fin 1024) := by decide
#print axioms hpos_leaf_116

theorem w0_leaf_116 : w0 116 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_942 (F := M)
  rw [hpos_leaf_116] at hs
  calc w0 116 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (116 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (116 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_116

theorem w2_leaf_116 : w2 116 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_942 (F := M)
  rw [hpos_leaf_116] at hs
  calc w2 116 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (116 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (116 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_116

theorem hpos_leaf_117 : order.symm (943 : Fin 1024) = (117 : Fin 1024) := by decide
#print axioms hpos_leaf_117

theorem w0_leaf_117 : w0 117 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_943 (F := M)
  rw [hpos_leaf_117] at hs
  calc w0 117 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (117 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (117 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_117

theorem w2_leaf_117 : w2 117 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_943 (F := M)
  rw [hpos_leaf_117] at hs
  calc w2 117 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (117 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (117 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_117

theorem hpos_leaf_118 : order.symm (958 : Fin 1024) = (118 : Fin 1024) := by decide
#print axioms hpos_leaf_118

theorem w0_leaf_118 : w0 118 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_958 (F := M)
  rw [hpos_leaf_118] at hs
  calc w0 118 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (118 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (118 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_118

theorem w2_leaf_118 : w2 118 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_958 (F := M)
  rw [hpos_leaf_118] at hs
  calc w2 118 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (118 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (118 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_118

theorem hpos_leaf_119 : order.symm (959 : Fin 1024) = (119 : Fin 1024) := by decide
#print axioms hpos_leaf_119

theorem w0_leaf_119 : w0 119 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_959 (F := M)
  rw [hpos_leaf_119] at hs
  calc w0 119 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (119 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (119 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_119

theorem w2_leaf_119 : w2 119 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_959 (F := M)
  rw [hpos_leaf_119] at hs
  calc w2 119 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (119 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (119 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_119

theorem hpos_leaf_120 : order.symm (974 : Fin 1024) = (120 : Fin 1024) := by decide
#print axioms hpos_leaf_120

theorem w0_leaf_120 : w0 120 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_974 (F := M)
  rw [hpos_leaf_120] at hs
  calc w0 120 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (120 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (120 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_120

theorem w2_leaf_120 : w2 120 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_974 (F := M)
  rw [hpos_leaf_120] at hs
  calc w2 120 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (120 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (120 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_120

theorem hpos_leaf_121 : order.symm (975 : Fin 1024) = (121 : Fin 1024) := by decide
#print axioms hpos_leaf_121

theorem w0_leaf_121 : w0 121 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_975 (F := M)
  rw [hpos_leaf_121] at hs
  calc w0 121 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (121 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (121 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_121

theorem w2_leaf_121 : w2 121 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_975 (F := M)
  rw [hpos_leaf_121] at hs
  calc w2 121 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (121 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (121 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_121

theorem hpos_leaf_122 : order.symm (990 : Fin 1024) = (122 : Fin 1024) := by decide
#print axioms hpos_leaf_122

theorem w0_leaf_122 : w0 122 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_990 (F := M)
  rw [hpos_leaf_122] at hs
  calc w0 122 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (122 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (122 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_122

theorem w2_leaf_122 : w2 122 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_990 (F := M)
  rw [hpos_leaf_122] at hs
  calc w2 122 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (122 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (122 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_122

theorem hpos_leaf_123 : order.symm (991 : Fin 1024) = (123 : Fin 1024) := by decide
#print axioms hpos_leaf_123

theorem w0_leaf_123 : w0 123 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_991 (F := M)
  rw [hpos_leaf_123] at hs
  calc w0 123 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (123 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (123 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_123

theorem w2_leaf_123 : w2 123 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_991 (F := M)
  rw [hpos_leaf_123] at hs
  calc w2 123 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (123 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (123 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_123

theorem hpos_leaf_124 : order.symm (1006 : Fin 1024) = (124 : Fin 1024) := by decide
#print axioms hpos_leaf_124

theorem w0_leaf_124 : w0 124 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_1006 (F := M)
  rw [hpos_leaf_124] at hs
  calc w0 124 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (124 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (124 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_124

theorem w2_leaf_124 : w2 124 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_1006 (F := M)
  rw [hpos_leaf_124] at hs
  calc w2 124 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (124 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (124 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_124

theorem hpos_leaf_125 : order.symm (1007 : Fin 1024) = (125 : Fin 1024) := by decide
#print axioms hpos_leaf_125

theorem w0_leaf_125 : w0 125 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_1007 (F := M)
  rw [hpos_leaf_125] at hs
  calc w0 125 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (125 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (125 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_125

theorem w2_leaf_125 : w2 125 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_1007 (F := M)
  rw [hpos_leaf_125] at hs
  calc w2 125 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (125 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (125 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_125

theorem hpos_leaf_126 : order.symm (993 : Fin 1024) = (126 : Fin 1024) := by decide
#print axioms hpos_leaf_126

theorem w0_leaf_126 : w0 126 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_993 (F := M)
  rw [hpos_leaf_126] at hs
  calc w0 126 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (126 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (126 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_126

theorem w2_leaf_126 : w2 126 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_993 (F := M)
  rw [hpos_leaf_126] at hs
  calc w2 126 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (126 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (126 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_126

theorem hpos_leaf_127 : order.symm (1009 : Fin 1024) = (127 : Fin 1024) := by decide
#print axioms hpos_leaf_127

theorem w0_leaf_127 : w0 127 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_1009 (F := M)
  rw [hpos_leaf_127] at hs
  calc w0 127 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (127 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (127 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_127

theorem w2_leaf_127 : w2 127 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_1009 (F := M)
  rw [hpos_leaf_127] at hs
  calc w2 127 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (127 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (127 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_127

theorem hpos_leaf_128 : order.symm (12 : Fin 1024) = (128 : Fin 1024) := by decide
#print axioms hpos_leaf_128

theorem w0_leaf_128 : w0 128 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_12 (F := M)
  rw [hpos_leaf_128] at hs
  calc w0 128 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (128 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (128 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_128

theorem w2_leaf_128 : w2 128 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_12 (F := M)
  rw [hpos_leaf_128] at hs
  calc w2 128 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (128 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (128 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_128

theorem hpos_leaf_129 : order.symm (13 : Fin 1024) = (129 : Fin 1024) := by decide
#print axioms hpos_leaf_129

theorem w0_leaf_129 : w0 129 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_13 (F := M)
  rw [hpos_leaf_129] at hs
  calc w0 129 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (129 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (129 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_129

theorem w2_leaf_129 : w2 129 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_13 (F := M)
  rw [hpos_leaf_129] at hs
  calc w2 129 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (129 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (129 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_129

theorem hpos_leaf_130 : order.symm (28 : Fin 1024) = (130 : Fin 1024) := by decide
#print axioms hpos_leaf_130

theorem w0_leaf_130 : w0 130 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_28 (F := M)
  rw [hpos_leaf_130] at hs
  calc w0 130 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (130 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (130 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_130

theorem w2_leaf_130 : w2 130 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_28 (F := M)
  rw [hpos_leaf_130] at hs
  calc w2 130 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (130 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (130 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_130

theorem hpos_leaf_131 : order.symm (29 : Fin 1024) = (131 : Fin 1024) := by decide
#print axioms hpos_leaf_131

theorem w0_leaf_131 : w0 131 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_29 (F := M)
  rw [hpos_leaf_131] at hs
  calc w0 131 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (131 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (131 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_131

theorem w2_leaf_131 : w2 131 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_29 (F := M)
  rw [hpos_leaf_131] at hs
  calc w2 131 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (131 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (131 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_131

theorem hpos_leaf_132 : order.symm (44 : Fin 1024) = (132 : Fin 1024) := by decide
#print axioms hpos_leaf_132

theorem w0_leaf_132 : w0 132 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_44 (F := M)
  rw [hpos_leaf_132] at hs
  calc w0 132 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (132 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (132 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_132

theorem w2_leaf_132 : w2 132 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_44 (F := M)
  rw [hpos_leaf_132] at hs
  calc w2 132 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (132 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (132 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_132

theorem hpos_leaf_133 : order.symm (45 : Fin 1024) = (133 : Fin 1024) := by decide
#print axioms hpos_leaf_133

theorem w0_leaf_133 : w0 133 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_45 (F := M)
  rw [hpos_leaf_133] at hs
  calc w0 133 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (133 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (133 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_133

theorem w2_leaf_133 : w2 133 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_45 (F := M)
  rw [hpos_leaf_133] at hs
  calc w2 133 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (133 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (133 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_133

theorem hpos_leaf_134 : order.symm (60 : Fin 1024) = (134 : Fin 1024) := by decide
#print axioms hpos_leaf_134

theorem w0_leaf_134 : w0 134 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_60 (F := M)
  rw [hpos_leaf_134] at hs
  calc w0 134 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (134 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (134 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_134

theorem w2_leaf_134 : w2 134 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_60 (F := M)
  rw [hpos_leaf_134] at hs
  calc w2 134 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (134 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (134 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_134

theorem hpos_leaf_135 : order.symm (61 : Fin 1024) = (135 : Fin 1024) := by decide
#print axioms hpos_leaf_135

theorem w0_leaf_135 : w0 135 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_61 (F := M)
  rw [hpos_leaf_135] at hs
  calc w0 135 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (135 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (135 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_135

theorem w2_leaf_135 : w2 135 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_61 (F := M)
  rw [hpos_leaf_135] at hs
  calc w2 135 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (135 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (135 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_135

theorem hpos_leaf_136 : order.symm (76 : Fin 1024) = (136 : Fin 1024) := by decide
#print axioms hpos_leaf_136

theorem w0_leaf_136 : w0 136 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_76 (F := M)
  rw [hpos_leaf_136] at hs
  calc w0 136 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (136 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (136 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_136

theorem w2_leaf_136 : w2 136 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_76 (F := M)
  rw [hpos_leaf_136] at hs
  calc w2 136 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (136 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (136 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_136

theorem hpos_leaf_137 : order.symm (77 : Fin 1024) = (137 : Fin 1024) := by decide
#print axioms hpos_leaf_137

theorem w0_leaf_137 : w0 137 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_77 (F := M)
  rw [hpos_leaf_137] at hs
  calc w0 137 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (137 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (137 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_137

theorem w2_leaf_137 : w2 137 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_77 (F := M)
  rw [hpos_leaf_137] at hs
  calc w2 137 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (137 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (137 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_137

theorem hpos_leaf_138 : order.symm (92 : Fin 1024) = (138 : Fin 1024) := by decide
#print axioms hpos_leaf_138

theorem w0_leaf_138 : w0 138 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_92 (F := M)
  rw [hpos_leaf_138] at hs
  calc w0 138 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (138 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (138 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_138

theorem w2_leaf_138 : w2 138 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_92 (F := M)
  rw [hpos_leaf_138] at hs
  calc w2 138 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (138 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (138 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_138

theorem hpos_leaf_139 : order.symm (93 : Fin 1024) = (139 : Fin 1024) := by decide
#print axioms hpos_leaf_139

theorem w0_leaf_139 : w0 139 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_93 (F := M)
  rw [hpos_leaf_139] at hs
  calc w0 139 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (139 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (139 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_139

theorem w2_leaf_139 : w2 139 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_93 (F := M)
  rw [hpos_leaf_139] at hs
  calc w2 139 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (139 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (139 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_139

theorem hpos_leaf_140 : order.symm (108 : Fin 1024) = (140 : Fin 1024) := by decide
#print axioms hpos_leaf_140

theorem w0_leaf_140 : w0 140 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_108 (F := M)
  rw [hpos_leaf_140] at hs
  calc w0 140 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (140 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (140 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_140

theorem w2_leaf_140 : w2 140 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_108 (F := M)
  rw [hpos_leaf_140] at hs
  calc w2 140 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (140 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (140 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_140

theorem hpos_leaf_141 : order.symm (109 : Fin 1024) = (141 : Fin 1024) := by decide
#print axioms hpos_leaf_141

theorem w0_leaf_141 : w0 141 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_109 (F := M)
  rw [hpos_leaf_141] at hs
  calc w0 141 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (141 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (141 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_141

theorem w2_leaf_141 : w2 141 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_109 (F := M)
  rw [hpos_leaf_141] at hs
  calc w2 141 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (141 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (141 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_141

theorem hpos_leaf_142 : order.symm (124 : Fin 1024) = (142 : Fin 1024) := by decide
#print axioms hpos_leaf_142

theorem w0_leaf_142 : w0 142 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_124 (F := M)
  rw [hpos_leaf_142] at hs
  calc w0 142 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (142 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (142 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_142

theorem w2_leaf_142 : w2 142 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_124 (F := M)
  rw [hpos_leaf_142] at hs
  calc w2 142 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (142 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (142 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_142

end
end AspisV8R19.R780Point02WeightSharedChunk01
