import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeaves
import AspisV8R19.R772Point02DualLeavesChunk00
import AspisV8R19.R772Point02DualLeavesChunk01

namespace AspisV8R19.R780Point02WeightSharedChunk00
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_0 : order.symm (14 : Fin 1024) = (0 : Fin 1024) := by decide
#print axioms hpos_leaf_0

theorem w0_leaf_0 : w0 0 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeaves.point0_guard14_transport_zero (F := M)
  rw [hpos_leaf_0] at hs
  calc w0 0 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (0 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (0 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_0

theorem w2_leaf_0 : w2 0 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeaves.point2_guard14_transport_zero (F := M)
  rw [hpos_leaf_0] at hs
  calc w2 0 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (0 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (0 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_0

theorem hpos_leaf_1 : order.symm (15 : Fin 1024) = (1 : Fin 1024) := by decide
#print axioms hpos_leaf_1

theorem w0_leaf_1 : w0 1 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_15 (F := M)
  rw [hpos_leaf_1] at hs
  calc w0 1 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_1

theorem w2_leaf_1 : w2 1 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_15 (F := M)
  rw [hpos_leaf_1] at hs
  calc w2 1 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_1

theorem hpos_leaf_2 : order.symm (30 : Fin 1024) = (2 : Fin 1024) := by decide
#print axioms hpos_leaf_2

theorem w0_leaf_2 : w0 2 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_30 (F := M)
  rw [hpos_leaf_2] at hs
  calc w0 2 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (2 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (2 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_2

theorem w2_leaf_2 : w2 2 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_30 (F := M)
  rw [hpos_leaf_2] at hs
  calc w2 2 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (2 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (2 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_2

theorem hpos_leaf_3 : order.symm (31 : Fin 1024) = (3 : Fin 1024) := by decide
#print axioms hpos_leaf_3

theorem w0_leaf_3 : w0 3 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_31 (F := M)
  rw [hpos_leaf_3] at hs
  calc w0 3 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (3 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (3 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_3

theorem w2_leaf_3 : w2 3 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_31 (F := M)
  rw [hpos_leaf_3] at hs
  calc w2 3 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (3 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (3 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_3

theorem hpos_leaf_4 : order.symm (46 : Fin 1024) = (4 : Fin 1024) := by decide
#print axioms hpos_leaf_4

theorem w0_leaf_4 : w0 4 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_46 (F := M)
  rw [hpos_leaf_4] at hs
  calc w0 4 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (4 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (4 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_4

theorem w2_leaf_4 : w2 4 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_46 (F := M)
  rw [hpos_leaf_4] at hs
  calc w2 4 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (4 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (4 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_4

theorem hpos_leaf_5 : order.symm (47 : Fin 1024) = (5 : Fin 1024) := by decide
#print axioms hpos_leaf_5

theorem w0_leaf_5 : w0 5 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_47 (F := M)
  rw [hpos_leaf_5] at hs
  calc w0 5 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (5 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (5 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_5

theorem w2_leaf_5 : w2 5 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_47 (F := M)
  rw [hpos_leaf_5] at hs
  calc w2 5 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (5 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (5 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_5

theorem hpos_leaf_6 : order.symm (62 : Fin 1024) = (6 : Fin 1024) := by decide
#print axioms hpos_leaf_6

theorem w0_leaf_6 : w0 6 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_62 (F := M)
  rw [hpos_leaf_6] at hs
  calc w0 6 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (6 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (6 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_6

theorem w2_leaf_6 : w2 6 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_62 (F := M)
  rw [hpos_leaf_6] at hs
  calc w2 6 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (6 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (6 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_6

theorem hpos_leaf_64 : order.symm (526 : Fin 1024) = (64 : Fin 1024) := by decide
#print axioms hpos_leaf_64

theorem w0_leaf_64 : w0 64 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_526 (F := M)
  rw [hpos_leaf_64] at hs
  calc w0 64 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (64 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (64 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_64

theorem w2_leaf_64 : w2 64 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_526 (F := M)
  rw [hpos_leaf_64] at hs
  calc w2 64 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (64 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (64 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_64

theorem hpos_leaf_65 : order.symm (527 : Fin 1024) = (65 : Fin 1024) := by decide
#print axioms hpos_leaf_65

theorem w0_leaf_65 : w0 65 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_527 (F := M)
  rw [hpos_leaf_65] at hs
  calc w0 65 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (65 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (65 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_65

theorem w2_leaf_65 : w2 65 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_527 (F := M)
  rw [hpos_leaf_65] at hs
  calc w2 65 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (65 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (65 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_65

theorem hpos_leaf_66 : order.symm (542 : Fin 1024) = (66 : Fin 1024) := by decide
#print axioms hpos_leaf_66

theorem w0_leaf_66 : w0 66 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_542 (F := M)
  rw [hpos_leaf_66] at hs
  calc w0 66 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (66 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (66 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_66

theorem w2_leaf_66 : w2 66 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_542 (F := M)
  rw [hpos_leaf_66] at hs
  calc w2 66 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (66 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (66 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_66

theorem hpos_leaf_80 : order.symm (654 : Fin 1024) = (80 : Fin 1024) := by decide
#print axioms hpos_leaf_80

theorem w0_leaf_80 : w0 80 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_654 (F := M)
  rw [hpos_leaf_80] at hs
  calc w0 80 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (80 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (80 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_80

theorem w2_leaf_80 : w2 80 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_654 (F := M)
  rw [hpos_leaf_80] at hs
  calc w2 80 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (80 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (80 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_80

theorem hpos_leaf_81 : order.symm (655 : Fin 1024) = (81 : Fin 1024) := by decide
#print axioms hpos_leaf_81

theorem w0_leaf_81 : w0 81 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_655 (F := M)
  rw [hpos_leaf_81] at hs
  calc w0 81 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (81 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (81 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_81

theorem w2_leaf_81 : w2 81 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_655 (F := M)
  rw [hpos_leaf_81] at hs
  calc w2 81 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (81 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (81 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_81

theorem hpos_leaf_82 : order.symm (670 : Fin 1024) = (82 : Fin 1024) := by decide
#print axioms hpos_leaf_82

theorem w0_leaf_82 : w0 82 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_670 (F := M)
  rw [hpos_leaf_82] at hs
  calc w0 82 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (82 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (82 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_82

theorem w2_leaf_82 : w2 82 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_670 (F := M)
  rw [hpos_leaf_82] at hs
  calc w2 82 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (82 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (82 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_82

theorem hpos_leaf_88 : order.symm (718 : Fin 1024) = (88 : Fin 1024) := by decide
#print axioms hpos_leaf_88

theorem w0_leaf_88 : w0 88 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_718 (F := M)
  rw [hpos_leaf_88] at hs
  calc w0 88 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (88 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (88 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_88

theorem w2_leaf_88 : w2 88 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_718 (F := M)
  rw [hpos_leaf_88] at hs
  calc w2 88 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (88 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (88 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_88

theorem hpos_leaf_89 : order.symm (719 : Fin 1024) = (89 : Fin 1024) := by decide
#print axioms hpos_leaf_89

theorem w0_leaf_89 : w0 89 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_719 (F := M)
  rw [hpos_leaf_89] at hs
  calc w0 89 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (89 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (89 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_89

theorem w2_leaf_89 : w2 89 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_719 (F := M)
  rw [hpos_leaf_89] at hs
  calc w2 89 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (89 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (89 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_89

theorem hpos_leaf_90 : order.symm (734 : Fin 1024) = (90 : Fin 1024) := by decide
#print axioms hpos_leaf_90

theorem w0_leaf_90 : w0 90 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_734 (F := M)
  rw [hpos_leaf_90] at hs
  calc w0 90 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (90 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (90 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_90

theorem w2_leaf_90 : w2 90 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_734 (F := M)
  rw [hpos_leaf_90] at hs
  calc w2 90 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (90 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (90 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_90

theorem hpos_leaf_92 : order.symm (750 : Fin 1024) = (92 : Fin 1024) := by decide
#print axioms hpos_leaf_92

theorem w0_leaf_92 : w0 92 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_750 (F := M)
  rw [hpos_leaf_92] at hs
  calc w0 92 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (92 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (92 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_92

theorem w2_leaf_92 : w2 92 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_750 (F := M)
  rw [hpos_leaf_92] at hs
  calc w2 92 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (92 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (92 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_92

theorem hpos_leaf_93 : order.symm (751 : Fin 1024) = (93 : Fin 1024) := by decide
#print axioms hpos_leaf_93

theorem w0_leaf_93 : w0 93 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_751 (F := M)
  rw [hpos_leaf_93] at hs
  calc w0 93 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (93 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (93 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_93

theorem w2_leaf_93 : w2 93 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_751 (F := M)
  rw [hpos_leaf_93] at hs
  calc w2 93 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (93 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (93 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_93

theorem hpos_leaf_94 : order.symm (766 : Fin 1024) = (94 : Fin 1024) := by decide
#print axioms hpos_leaf_94

theorem w0_leaf_94 : w0 94 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_766 (F := M)
  rw [hpos_leaf_94] at hs
  calc w0 94 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (94 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (94 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_94

theorem w2_leaf_94 : w2 94 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_766 (F := M)
  rw [hpos_leaf_94] at hs
  calc w2 94 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (94 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (94 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_94

theorem hpos_leaf_95 : order.symm (767 : Fin 1024) = (95 : Fin 1024) := by decide
#print axioms hpos_leaf_95

theorem w0_leaf_95 : w0 95 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_767 (F := M)
  rw [hpos_leaf_95] at hs
  calc w0 95 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (95 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (95 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_95

theorem w2_leaf_95 : w2 95 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_767 (F := M)
  rw [hpos_leaf_95] at hs
  calc w2 95 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (95 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (95 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_95

theorem hpos_leaf_96 : order.symm (782 : Fin 1024) = (96 : Fin 1024) := by decide
#print axioms hpos_leaf_96

theorem w0_leaf_96 : w0 96 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_782 (F := M)
  rw [hpos_leaf_96] at hs
  calc w0 96 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (96 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (96 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_96

theorem w2_leaf_96 : w2 96 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_782 (F := M)
  rw [hpos_leaf_96] at hs
  calc w2 96 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (96 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (96 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_96

theorem hpos_leaf_97 : order.symm (783 : Fin 1024) = (97 : Fin 1024) := by decide
#print axioms hpos_leaf_97

theorem w0_leaf_97 : w0 97 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_783 (F := M)
  rw [hpos_leaf_97] at hs
  calc w0 97 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (97 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (97 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_97

theorem w2_leaf_97 : w2 97 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_783 (F := M)
  rw [hpos_leaf_97] at hs
  calc w2 97 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (97 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (97 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_97

theorem hpos_leaf_98 : order.symm (798 : Fin 1024) = (98 : Fin 1024) := by decide
#print axioms hpos_leaf_98

theorem w0_leaf_98 : w0 98 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_798 (F := M)
  rw [hpos_leaf_98] at hs
  calc w0 98 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (98 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (98 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_98

theorem w2_leaf_98 : w2 98 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_798 (F := M)
  rw [hpos_leaf_98] at hs
  calc w2 98 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (98 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (98 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_98

theorem hpos_leaf_99 : order.symm (799 : Fin 1024) = (99 : Fin 1024) := by decide
#print axioms hpos_leaf_99

theorem w0_leaf_99 : w0 99 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_799 (F := M)
  rw [hpos_leaf_99] at hs
  calc w0 99 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (99 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (99 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_99

theorem w2_leaf_99 : w2 99 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_799 (F := M)
  rw [hpos_leaf_99] at hs
  calc w2 99 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (99 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (99 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_99

theorem hpos_leaf_100 : order.symm (814 : Fin 1024) = (100 : Fin 1024) := by decide
#print axioms hpos_leaf_100

theorem w0_leaf_100 : w0 100 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_814 (F := M)
  rw [hpos_leaf_100] at hs
  calc w0 100 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (100 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (100 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_100

theorem w2_leaf_100 : w2 100 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_814 (F := M)
  rw [hpos_leaf_100] at hs
  calc w2 100 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (100 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (100 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_100

theorem hpos_leaf_101 : order.symm (815 : Fin 1024) = (101 : Fin 1024) := by decide
#print axioms hpos_leaf_101

theorem w0_leaf_101 : w0 101 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_815 (F := M)
  rw [hpos_leaf_101] at hs
  calc w0 101 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (101 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (101 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_101

theorem w2_leaf_101 : w2 101 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_815 (F := M)
  rw [hpos_leaf_101] at hs
  calc w2 101 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (101 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (101 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_101

theorem hpos_leaf_102 : order.symm (830 : Fin 1024) = (102 : Fin 1024) := by decide
#print axioms hpos_leaf_102

theorem w0_leaf_102 : w0 102 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_830 (F := M)
  rw [hpos_leaf_102] at hs
  calc w0 102 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (102 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (102 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_102

theorem w2_leaf_102 : w2 102 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_830 (F := M)
  rw [hpos_leaf_102] at hs
  calc w2 102 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (102 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (102 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_102

theorem hpos_leaf_105 : order.symm (847 : Fin 1024) = (105 : Fin 1024) := by decide
#print axioms hpos_leaf_105

theorem w0_leaf_105 : w0 105 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_847 (F := M)
  rw [hpos_leaf_105] at hs
  calc w0 105 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (105 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (105 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_105

theorem w2_leaf_105 : w2 105 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_847 (F := M)
  rw [hpos_leaf_105] at hs
  calc w2 105 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (105 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (105 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_105

theorem hpos_leaf_106 : order.symm (862 : Fin 1024) = (106 : Fin 1024) := by decide
#print axioms hpos_leaf_106

theorem w0_leaf_106 : w0 106 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_862 (F := M)
  rw [hpos_leaf_106] at hs
  calc w0 106 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (106 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (106 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_106

theorem w2_leaf_106 : w2 106 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_862 (F := M)
  rw [hpos_leaf_106] at hs
  calc w2 106 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (106 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (106 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_106

theorem hpos_leaf_108 : order.symm (878 : Fin 1024) = (108 : Fin 1024) := by decide
#print axioms hpos_leaf_108

theorem w0_leaf_108 : w0 108 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_878 (F := M)
  rw [hpos_leaf_108] at hs
  calc w0 108 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (108 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (108 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_108

theorem w2_leaf_108 : w2 108 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_878 (F := M)
  rw [hpos_leaf_108] at hs
  calc w2 108 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (108 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (108 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_108

theorem hpos_leaf_109 : order.symm (879 : Fin 1024) = (109 : Fin 1024) := by decide
#print axioms hpos_leaf_109

theorem w0_leaf_109 : w0 109 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_879 (F := M)
  rw [hpos_leaf_109] at hs
  calc w0 109 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (109 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (109 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_109

theorem w2_leaf_109 : w2 109 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_879 (F := M)
  rw [hpos_leaf_109] at hs
  calc w2 109 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (109 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (109 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_109

theorem hpos_leaf_110 : order.symm (894 : Fin 1024) = (110 : Fin 1024) := by decide
#print axioms hpos_leaf_110

theorem w0_leaf_110 : w0 110 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p0_transport_zero_original_894 (F := M)
  rw [hpos_leaf_110] at hs
  calc w0 110 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (110 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (110 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_110

theorem w2_leaf_110 : w2 110 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk01.p2_transport_zero_original_894 (F := M)
  rw [hpos_leaf_110] at hs
  calc w2 110 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (110 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (110 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_110

end
end AspisV8R19.R780Point02WeightSharedChunk00
