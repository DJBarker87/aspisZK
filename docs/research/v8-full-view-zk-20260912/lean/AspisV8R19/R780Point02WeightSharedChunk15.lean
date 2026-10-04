import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk15
import AspisV8R19.R772Point02DualLeavesChunk25
import AspisV8R19.R772Point02DualLeavesChunk26
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk28
import AspisV8R19.R772Point02DualLeavesChunk31
import AspisV8R19.R772Point02DualLeavesChunk32

namespace AspisV8R19.R780Point02WeightSharedChunk15
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_984 : order.symm (704 : Fin 1024) = (984 : Fin 1024) := by decide
#print axioms hpos_leaf_984

theorem w0_leaf_984 : w0 984 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_704 (F := M)
  rw [hpos_leaf_984] at hs
  calc w0 984 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (984 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (984 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_984

theorem w2_leaf_984 : w2 984 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_704 (F := M)
  rw [hpos_leaf_984] at hs
  calc w2 984 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (984 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (984 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_984

theorem hpos_leaf_985 : order.symm (705 : Fin 1024) = (985 : Fin 1024) := by decide
#print axioms hpos_leaf_985

theorem w0_leaf_985 : w0 985 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_705 (F := M)
  rw [hpos_leaf_985] at hs
  calc w0 985 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (985 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (985 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_985

theorem w2_leaf_985 : w2 985 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_705 (F := M)
  rw [hpos_leaf_985] at hs
  calc w2 985 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (985 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (985 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_985

theorem hpos_leaf_986 : order.symm (720 : Fin 1024) = (986 : Fin 1024) := by decide
#print axioms hpos_leaf_986

theorem w0_leaf_986 : w0 986 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_720 (F := M)
  rw [hpos_leaf_986] at hs
  calc w0 986 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (986 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (986 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_986

theorem w2_leaf_986 : w2 986 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_720 (F := M)
  rw [hpos_leaf_986] at hs
  calc w2 986 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (986 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (986 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_986

theorem hpos_leaf_987 : order.symm (721 : Fin 1024) = (987 : Fin 1024) := by decide
#print axioms hpos_leaf_987

theorem w0_leaf_987 : w0 987 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_721 (F := M)
  rw [hpos_leaf_987] at hs
  calc w0 987 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (987 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (987 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_987

theorem w2_leaf_987 : w2 987 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_721 (F := M)
  rw [hpos_leaf_987] at hs
  calc w2 987 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (987 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (987 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_987

theorem hpos_leaf_988 : order.symm (736 : Fin 1024) = (988 : Fin 1024) := by decide
#print axioms hpos_leaf_988

theorem w0_leaf_988 : w0 988 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_zero_original_736 (F := M)
  rw [hpos_leaf_988] at hs
  calc w0 988 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (988 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (988 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_988

theorem w2_leaf_988 : w2 988 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_zero_original_736 (F := M)
  rw [hpos_leaf_988] at hs
  calc w2 988 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (988 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (988 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_988

theorem hpos_leaf_989 : order.symm (737 : Fin 1024) = (989 : Fin 1024) := by decide
#print axioms hpos_leaf_989

theorem w0_leaf_989 : w0 989 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_737 (F := M)
  rw [hpos_leaf_989] at hs
  calc w0 989 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (989 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (989 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_989

theorem w2_leaf_989 : w2 989 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_737 (F := M)
  rw [hpos_leaf_989] at hs
  calc w2 989 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (989 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (989 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_989

theorem hpos_leaf_990 : order.symm (752 : Fin 1024) = (990 : Fin 1024) := by decide
#print axioms hpos_leaf_990

theorem w0_leaf_990 : w0 990 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_zero_original_752 (F := M)
  rw [hpos_leaf_990] at hs
  calc w0 990 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (990 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (990 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_990

theorem w2_leaf_990 : w2 990 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_zero_original_752 (F := M)
  rw [hpos_leaf_990] at hs
  calc w2 990 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (990 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (990 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_990

theorem hpos_leaf_991 : order.symm (753 : Fin 1024) = (991 : Fin 1024) := by decide
#print axioms hpos_leaf_991

theorem w0_leaf_991 : w0 991 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_753 (F := M)
  rw [hpos_leaf_991] at hs
  calc w0 991 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (991 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (991 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_991

theorem w2_leaf_991 : w2 991 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_753 (F := M)
  rw [hpos_leaf_991] at hs
  calc w2 991 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (991 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (991 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_991

theorem hpos_leaf_992 : order.symm (768 : Fin 1024) = (992 : Fin 1024) := by decide
#print axioms hpos_leaf_992

theorem w0_leaf_992 : w0 992 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_768 (F := M)
  rw [hpos_leaf_992] at hs
  calc w0 992 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (992 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (992 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_992

theorem w2_leaf_992 : w2 992 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_768 (F := M)
  rw [hpos_leaf_992] at hs
  calc w2 992 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (992 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (992 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_992

theorem hpos_leaf_993 : order.symm (769 : Fin 1024) = (993 : Fin 1024) := by decide
#print axioms hpos_leaf_993

theorem w0_leaf_993 : w0 993 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_769 (F := M)
  rw [hpos_leaf_993] at hs
  calc w0 993 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (993 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (993 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_993

theorem w2_leaf_993 : w2 993 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_769 (F := M)
  rw [hpos_leaf_993] at hs
  calc w2 993 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (993 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (993 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_993

theorem hpos_leaf_994 : order.symm (784 : Fin 1024) = (994 : Fin 1024) := by decide
#print axioms hpos_leaf_994

theorem w0_leaf_994 : w0 994 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_784 (F := M)
  rw [hpos_leaf_994] at hs
  calc w0 994 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (994 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (994 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_994

theorem w2_leaf_994 : w2 994 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_784 (F := M)
  rw [hpos_leaf_994] at hs
  calc w2 994 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (994 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (994 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_994

theorem hpos_leaf_995 : order.symm (785 : Fin 1024) = (995 : Fin 1024) := by decide
#print axioms hpos_leaf_995

theorem w0_leaf_995 : w0 995 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_785 (F := M)
  rw [hpos_leaf_995] at hs
  calc w0 995 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (995 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (995 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_995

theorem w2_leaf_995 : w2 995 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_785 (F := M)
  rw [hpos_leaf_995] at hs
  calc w2 995 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (995 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (995 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_995

theorem hpos_leaf_996 : order.symm (800 : Fin 1024) = (996 : Fin 1024) := by decide
#print axioms hpos_leaf_996

theorem w0_leaf_996 : w0 996 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_800 (F := M)
  rw [hpos_leaf_996] at hs
  calc w0 996 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (996 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (996 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_996

theorem w2_leaf_996 : w2 996 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_800 (F := M)
  rw [hpos_leaf_996] at hs
  calc w2 996 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (996 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (996 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_996

theorem hpos_leaf_997 : order.symm (801 : Fin 1024) = (997 : Fin 1024) := by decide
#print axioms hpos_leaf_997

theorem w0_leaf_997 : w0 997 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_801 (F := M)
  rw [hpos_leaf_997] at hs
  calc w0 997 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (997 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (997 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_997

theorem w2_leaf_997 : w2 997 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_801 (F := M)
  rw [hpos_leaf_997] at hs
  calc w2 997 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (997 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (997 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_997

theorem hpos_leaf_998 : order.symm (816 : Fin 1024) = (998 : Fin 1024) := by decide
#print axioms hpos_leaf_998

theorem w0_leaf_998 : w0 998 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_816 (F := M)
  rw [hpos_leaf_998] at hs
  calc w0 998 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (998 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (998 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_998

theorem w2_leaf_998 : w2 998 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_816 (F := M)
  rw [hpos_leaf_998] at hs
  calc w2 998 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (998 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (998 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_998

theorem hpos_leaf_999 : order.symm (817 : Fin 1024) = (999 : Fin 1024) := by decide
#print axioms hpos_leaf_999

theorem w0_leaf_999 : w0 999 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_817 (F := M)
  rw [hpos_leaf_999] at hs
  calc w0 999 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (999 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (999 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_999

theorem w2_leaf_999 : w2 999 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_817 (F := M)
  rw [hpos_leaf_999] at hs
  calc w2 999 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (999 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (999 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_999

theorem hpos_leaf_1000 : order.symm (832 : Fin 1024) = (1000 : Fin 1024) := by decide
#print axioms hpos_leaf_1000

theorem w0_leaf_1000 : w0 1000 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_832 (F := M)
  rw [hpos_leaf_1000] at hs
  calc w0 1000 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1000 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1000 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1000

theorem w2_leaf_1000 : w2 1000 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_832 (F := M)
  rw [hpos_leaf_1000] at hs
  calc w2 1000 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1000 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1000 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1000

theorem hpos_leaf_1001 : order.symm (833 : Fin 1024) = (1001 : Fin 1024) := by decide
#print axioms hpos_leaf_1001

theorem w0_leaf_1001 : w0 1001 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_833 (F := M)
  rw [hpos_leaf_1001] at hs
  calc w0 1001 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1001 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1001 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1001

theorem w2_leaf_1001 : w2 1001 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_833 (F := M)
  rw [hpos_leaf_1001] at hs
  calc w2 1001 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1001 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1001 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1001

theorem hpos_leaf_1002 : order.symm (848 : Fin 1024) = (1002 : Fin 1024) := by decide
#print axioms hpos_leaf_1002

theorem w0_leaf_1002 : w0 1002 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_848 (F := M)
  rw [hpos_leaf_1002] at hs
  calc w0 1002 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1002 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1002 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1002

theorem w2_leaf_1002 : w2 1002 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_848 (F := M)
  rw [hpos_leaf_1002] at hs
  calc w2 1002 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1002 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1002 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1002

theorem hpos_leaf_1003 : order.symm (849 : Fin 1024) = (1003 : Fin 1024) := by decide
#print axioms hpos_leaf_1003

theorem w0_leaf_1003 : w0 1003 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_849 (F := M)
  rw [hpos_leaf_1003] at hs
  calc w0 1003 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1003 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1003 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1003

theorem w2_leaf_1003 : w2 1003 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_849 (F := M)
  rw [hpos_leaf_1003] at hs
  calc w2 1003 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1003 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1003 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1003

theorem hpos_leaf_1004 : order.symm (864 : Fin 1024) = (1004 : Fin 1024) := by decide
#print axioms hpos_leaf_1004

theorem w0_leaf_1004 : w0 1004 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_864 (F := M)
  rw [hpos_leaf_1004] at hs
  calc w0 1004 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1004 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1004 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1004

theorem w2_leaf_1004 : w2 1004 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_864 (F := M)
  rw [hpos_leaf_1004] at hs
  calc w2 1004 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1004 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1004 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1004

theorem hpos_leaf_1005 : order.symm (865 : Fin 1024) = (1005 : Fin 1024) := by decide
#print axioms hpos_leaf_1005

theorem w0_leaf_1005 : w0 1005 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_865 (F := M)
  rw [hpos_leaf_1005] at hs
  calc w0 1005 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1005 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1005 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1005

theorem w2_leaf_1005 : w2 1005 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_865 (F := M)
  rw [hpos_leaf_1005] at hs
  calc w2 1005 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1005 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1005 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1005

theorem hpos_leaf_1006 : order.symm (880 : Fin 1024) = (1006 : Fin 1024) := by decide
#print axioms hpos_leaf_1006

theorem w0_leaf_1006 : w0 1006 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_880 (F := M)
  rw [hpos_leaf_1006] at hs
  calc w0 1006 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1006 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1006 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1006

theorem w2_leaf_1006 : w2 1006 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_880 (F := M)
  rw [hpos_leaf_1006] at hs
  calc w2 1006 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1006 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1006 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1006

theorem hpos_leaf_1007 : order.symm (881 : Fin 1024) = (1007 : Fin 1024) := by decide
#print axioms hpos_leaf_1007

theorem w0_leaf_1007 : w0 1007 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_881 (F := M)
  rw [hpos_leaf_1007] at hs
  calc w0 1007 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1007 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1007 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1007

theorem w2_leaf_1007 : w2 1007 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_881 (F := M)
  rw [hpos_leaf_1007] at hs
  calc w2 1007 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1007 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1007 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1007

theorem hpos_leaf_1008 : order.symm (896 : Fin 1024) = (1008 : Fin 1024) := by decide
#print axioms hpos_leaf_1008

theorem w0_leaf_1008 : w0 1008 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_896 (F := M)
  rw [hpos_leaf_1008] at hs
  calc w0 1008 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1008 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1008 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1008

theorem w2_leaf_1008 : w2 1008 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_896 (F := M)
  rw [hpos_leaf_1008] at hs
  calc w2 1008 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1008 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1008 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1008

theorem hpos_leaf_1009 : order.symm (897 : Fin 1024) = (1009 : Fin 1024) := by decide
#print axioms hpos_leaf_1009

theorem w0_leaf_1009 : w0 1009 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_897 (F := M)
  rw [hpos_leaf_1009] at hs
  calc w0 1009 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1009 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1009 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1009

theorem w2_leaf_1009 : w2 1009 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_897 (F := M)
  rw [hpos_leaf_1009] at hs
  calc w2 1009 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1009 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1009 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1009

theorem hpos_leaf_1010 : order.symm (912 : Fin 1024) = (1010 : Fin 1024) := by decide
#print axioms hpos_leaf_1010

theorem w0_leaf_1010 : w0 1010 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_912 (F := M)
  rw [hpos_leaf_1010] at hs
  calc w0 1010 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1010 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1010 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1010

theorem w2_leaf_1010 : w2 1010 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_912 (F := M)
  rw [hpos_leaf_1010] at hs
  calc w2 1010 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1010 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1010 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1010

theorem hpos_leaf_1011 : order.symm (913 : Fin 1024) = (1011 : Fin 1024) := by decide
#print axioms hpos_leaf_1011

theorem w0_leaf_1011 : w0 1011 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_913 (F := M)
  rw [hpos_leaf_1011] at hs
  calc w0 1011 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1011 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1011 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1011

theorem w2_leaf_1011 : w2 1011 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_913 (F := M)
  rw [hpos_leaf_1011] at hs
  calc w2 1011 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1011 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1011 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1011

theorem hpos_leaf_1012 : order.symm (928 : Fin 1024) = (1012 : Fin 1024) := by decide
#print axioms hpos_leaf_1012

theorem w0_leaf_1012 : w0 1012 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_928 (F := M)
  rw [hpos_leaf_1012] at hs
  calc w0 1012 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1012 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1012 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1012

theorem w2_leaf_1012 : w2 1012 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_928 (F := M)
  rw [hpos_leaf_1012] at hs
  calc w2 1012 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1012 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1012 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1012

theorem hpos_leaf_1013 : order.symm (929 : Fin 1024) = (1013 : Fin 1024) := by decide
#print axioms hpos_leaf_1013

theorem w0_leaf_1013 : w0 1013 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_929 (F := M)
  rw [hpos_leaf_1013] at hs
  calc w0 1013 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1013 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1013 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1013

theorem w2_leaf_1013 : w2 1013 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_929 (F := M)
  rw [hpos_leaf_1013] at hs
  calc w2 1013 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1013 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1013 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1013

theorem hpos_leaf_1014 : order.symm (944 : Fin 1024) = (1014 : Fin 1024) := by decide
#print axioms hpos_leaf_1014

theorem w0_leaf_1014 : w0 1014 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p0_transport_exact_original_944 (F := M)
  rw [hpos_leaf_1014] at hs
  calc w0 1014 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1014 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1014 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_1014

theorem w2_leaf_1014 : w2 1014 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk32.p2_transport_exact_original_944 (F := M)
  rw [hpos_leaf_1014] at hs
  calc w2 1014 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1014 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1014 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_1014

theorem hpos_leaf_1015 : order.symm (945 : Fin 1024) = (1015 : Fin 1024) := by decide
#print axioms hpos_leaf_1015

theorem w0_leaf_1015 : w0 1015 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_945 (F := M)
  rw [hpos_leaf_1015] at hs
  calc w0 1015 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1015 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (1015 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_1015

theorem w2_leaf_1015 : w2 1015 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_945 (F := M)
  rw [hpos_leaf_1015] at hs
  calc w2 1015 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1015 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (1015 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_1015

end
end AspisV8R19.R780Point02WeightSharedChunk15
