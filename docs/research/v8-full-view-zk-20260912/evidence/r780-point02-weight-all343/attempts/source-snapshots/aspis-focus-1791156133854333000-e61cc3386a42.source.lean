import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk15
import AspisV8R19.R772Point02DualLeavesChunk28
import AspisV8R19.R772Point02DualLeavesChunk32

namespace AspisV8R19.R780Point02WeightSharedChunk16
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_1016 : order.symm (960 : Fin 1024) = (1016 : Fin 1024) := by decide
#print axioms hpos_leaf_1016

theorem w0_leaf_1016 : w0 1016 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_960 (F := M)
  rw [hpos_leaf_1016] at hs
  calc w0 1016 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1016 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1016 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1016

theorem w2_leaf_1016 : w2 1016 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_960 (F := M)
  rw [hpos_leaf_1016] at hs
  calc w2 1016 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1016 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1016 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1016

theorem hpos_leaf_1017 : order.symm (961 : Fin 1024) = (1017 : Fin 1024) := by decide
#print axioms hpos_leaf_1017

theorem w0_leaf_1017 : w0 1017 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_961 (F := M)
  rw [hpos_leaf_1017] at hs
  calc w0 1017 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1017 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1017 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1017

theorem w2_leaf_1017 : w2 1017 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_961 (F := M)
  rw [hpos_leaf_1017] at hs
  calc w2 1017 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1017 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1017 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1017

theorem hpos_leaf_1018 : order.symm (976 : Fin 1024) = (1018 : Fin 1024) := by decide
#print axioms hpos_leaf_1018

theorem w0_leaf_1018 : w0 1018 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_976 (F := M)
  rw [hpos_leaf_1018] at hs
  calc w0 1018 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1018 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1018 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1018

theorem w2_leaf_1018 : w2 1018 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_976 (F := M)
  rw [hpos_leaf_1018] at hs
  calc w2 1018 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1018 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1018 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1018

theorem hpos_leaf_1019 : order.symm (977 : Fin 1024) = (1019 : Fin 1024) := by decide
#print axioms hpos_leaf_1019

theorem w0_leaf_1019 : w0 1019 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_977 (F := M)
  rw [hpos_leaf_1019] at hs
  calc w0 1019 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1019 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1019 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1019

theorem w2_leaf_1019 : w2 1019 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_977 (F := M)
  rw [hpos_leaf_1019] at hs
  calc w2 1019 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1019 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1019 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1019

theorem hpos_leaf_1020 : order.symm (992 : Fin 1024) = (1020 : Fin 1024) := by decide
#print axioms hpos_leaf_1020

theorem w0_leaf_1020 : w0 1020 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_992 (F := M)
  rw [hpos_leaf_1020] at hs
  calc w0 1020 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1020 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1020 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1020

theorem w2_leaf_1020 : w2 1020 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_992 (F := M)
  rw [hpos_leaf_1020] at hs
  calc w2 1020 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1020 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1020 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1020

theorem hpos_leaf_1021 : order.symm (1022 : Fin 1024) = (1021 : Fin 1024) := by decide
#print axioms hpos_leaf_1021

theorem w0_leaf_1021 : w0 1021 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_1022 (F := M)
  rw [hpos_leaf_1021] at hs
  calc w0 1021 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1021 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1021 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_1021

theorem w2_leaf_1021 : w2 1021 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_1022 (F := M)
  rw [hpos_leaf_1021] at hs
  calc w2 1021 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1021 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1021 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_1021

theorem hpos_leaf_1022 : order.symm (1008 : Fin 1024) = (1022 : Fin 1024) := by decide
#print axioms hpos_leaf_1022

theorem w0_leaf_1022 : w0 1022 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_1008 (F := M)
  rw [hpos_leaf_1022] at hs
  calc w0 1022 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1022 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1022 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1022

theorem w2_leaf_1022 : w2 1022 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_1008 (F := M)
  rw [hpos_leaf_1022] at hs
  calc w2 1022 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1022 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1022 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1022

end
end AspisV8R19.R780Point02WeightSharedChunk16
