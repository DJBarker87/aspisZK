import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk10
import AspisV8R19.R772Point02DualLeavesChunk11
import AspisV8R19.R772Point02DualLeavesChunk22
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk30

namespace AspisV8R19.R780Point02WeightSharedChunk10
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_502 : order.symm (952 : Fin 1024) = (502 : Fin 1024) := by decide
#print axioms hpos_leaf_502

theorem w0_leaf_502 : w0 502 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_952 (F := M)
  rw [hpos_leaf_502] at hs
  calc w0 502 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (502 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (502 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_502

theorem w2_leaf_502 : w2 502 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_952 (F := M)
  rw [hpos_leaf_502] at hs
  calc w2 502 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (502 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (502 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_502

theorem hpos_leaf_503 : order.symm (953 : Fin 1024) = (503 : Fin 1024) := by decide
#print axioms hpos_leaf_503

theorem w0_leaf_503 : w0 503 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_953 (F := M)
  rw [hpos_leaf_503] at hs
  calc w0 503 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (503 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (503 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_503

theorem w2_leaf_503 : w2 503 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_953 (F := M)
  rw [hpos_leaf_503] at hs
  calc w2 503 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (503 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (503 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_503

theorem hpos_leaf_504 : order.symm (968 : Fin 1024) = (504 : Fin 1024) := by decide
#print axioms hpos_leaf_504

theorem w0_leaf_504 : w0 504 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_968 (F := M)
  rw [hpos_leaf_504] at hs
  calc w0 504 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (504 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (504 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_504

theorem w2_leaf_504 : w2 504 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_968 (F := M)
  rw [hpos_leaf_504] at hs
  calc w2 504 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (504 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (504 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_504

theorem hpos_leaf_505 : order.symm (969 : Fin 1024) = (505 : Fin 1024) := by decide
#print axioms hpos_leaf_505

theorem w0_leaf_505 : w0 505 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_969 (F := M)
  rw [hpos_leaf_505] at hs
  calc w0 505 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (505 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (505 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_505

theorem w2_leaf_505 : w2 505 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_969 (F := M)
  rw [hpos_leaf_505] at hs
  calc w2 505 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (505 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (505 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_505

theorem hpos_leaf_506 : order.symm (984 : Fin 1024) = (506 : Fin 1024) := by decide
#print axioms hpos_leaf_506

theorem w0_leaf_506 : w0 506 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_984 (F := M)
  rw [hpos_leaf_506] at hs
  calc w0 506 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (506 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (506 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_506

theorem w2_leaf_506 : w2 506 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_984 (F := M)
  rw [hpos_leaf_506] at hs
  calc w2 506 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (506 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (506 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_506

theorem hpos_leaf_507 : order.symm (985 : Fin 1024) = (507 : Fin 1024) := by decide
#print axioms hpos_leaf_507

theorem w0_leaf_507 : w0 507 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_985 (F := M)
  rw [hpos_leaf_507] at hs
  calc w0 507 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (507 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (507 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_507

theorem w2_leaf_507 : w2 507 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_985 (F := M)
  rw [hpos_leaf_507] at hs
  calc w2 507 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (507 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (507 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_507

theorem hpos_leaf_508 : order.symm (1000 : Fin 1024) = (508 : Fin 1024) := by decide
#print axioms hpos_leaf_508

theorem w0_leaf_508 : w0 508 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_1000 (F := M)
  rw [hpos_leaf_508] at hs
  calc w0 508 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (508 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (508 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_508

theorem w2_leaf_508 : w2 508 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_1000 (F := M)
  rw [hpos_leaf_508] at hs
  calc w2 508 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (508 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (508 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_508

theorem hpos_leaf_509 : order.symm (1001 : Fin 1024) = (509 : Fin 1024) := by decide
#print axioms hpos_leaf_509

theorem w0_leaf_509 : w0 509 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1001 (F := M)
  rw [hpos_leaf_509] at hs
  calc w0 509 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (509 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (509 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_509

theorem w2_leaf_509 : w2 509 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1001 (F := M)
  rw [hpos_leaf_509] at hs
  calc w2 509 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (509 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (509 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_509

theorem hpos_leaf_510 : order.symm (1016 : Fin 1024) = (510 : Fin 1024) := by decide
#print axioms hpos_leaf_510

theorem w0_leaf_510 : w0 510 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_1016 (F := M)
  rw [hpos_leaf_510] at hs
  calc w0 510 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (510 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (510 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_510

theorem w2_leaf_510 : w2 510 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_1016 (F := M)
  rw [hpos_leaf_510] at hs
  calc w2 510 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (510 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (510 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_510

theorem hpos_leaf_511 : order.symm (1017 : Fin 1024) = (511 : Fin 1024) := by decide
#print axioms hpos_leaf_511

theorem w0_leaf_511 : w0 511 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1017 (F := M)
  rw [hpos_leaf_511] at hs
  calc w0 511 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (511 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (511 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_511

theorem w2_leaf_511 : w2 511 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1017 (F := M)
  rw [hpos_leaf_511] at hs
  calc w2 511 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (511 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (511 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_511

theorem hpos_leaf_512 : order.symm (6 : Fin 1024) = (512 : Fin 1024) := by decide
#print axioms hpos_leaf_512

theorem w0_leaf_512 : w0 512 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_6 (F := M)
  rw [hpos_leaf_512] at hs
  calc w0 512 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (512 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (512 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_512

theorem w2_leaf_512 : w2 512 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_6 (F := M)
  rw [hpos_leaf_512] at hs
  calc w2 512 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (512 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (512 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_512

theorem hpos_leaf_513 : order.symm (7 : Fin 1024) = (513 : Fin 1024) := by decide
#print axioms hpos_leaf_513

theorem w0_leaf_513 : w0 513 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_7 (F := M)
  rw [hpos_leaf_513] at hs
  calc w0 513 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (513 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (513 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_513

theorem w2_leaf_513 : w2 513 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_7 (F := M)
  rw [hpos_leaf_513] at hs
  calc w2 513 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (513 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (513 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_513

theorem hpos_leaf_514 : order.symm (22 : Fin 1024) = (514 : Fin 1024) := by decide
#print axioms hpos_leaf_514

theorem w0_leaf_514 : w0 514 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_22 (F := M)
  rw [hpos_leaf_514] at hs
  calc w0 514 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (514 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (514 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_514

theorem w2_leaf_514 : w2 514 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_22 (F := M)
  rw [hpos_leaf_514] at hs
  calc w2 514 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (514 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (514 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_514

theorem hpos_leaf_576 : order.symm (518 : Fin 1024) = (576 : Fin 1024) := by decide
#print axioms hpos_leaf_576

theorem w0_leaf_576 : w0 576 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_518 (F := M)
  rw [hpos_leaf_576] at hs
  calc w0 576 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (576 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (576 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_576

theorem w2_leaf_576 : w2 576 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_518 (F := M)
  rw [hpos_leaf_576] at hs
  calc w2 576 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (576 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (576 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_576

theorem hpos_leaf_577 : order.symm (519 : Fin 1024) = (577 : Fin 1024) := by decide
#print axioms hpos_leaf_577

theorem w0_leaf_577 : w0 577 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_519 (F := M)
  rw [hpos_leaf_577] at hs
  calc w0 577 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (577 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (577 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_577

theorem w2_leaf_577 : w2 577 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_519 (F := M)
  rw [hpos_leaf_577] at hs
  calc w2 577 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (577 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (577 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_577

theorem hpos_leaf_578 : order.symm (534 : Fin 1024) = (578 : Fin 1024) := by decide
#print axioms hpos_leaf_578

theorem w0_leaf_578 : w0 578 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_534 (F := M)
  rw [hpos_leaf_578] at hs
  calc w0 578 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (578 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (578 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_578

theorem w2_leaf_578 : w2 578 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_534 (F := M)
  rw [hpos_leaf_578] at hs
  calc w2 578 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (578 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (578 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_578

theorem hpos_leaf_608 : order.symm (774 : Fin 1024) = (608 : Fin 1024) := by decide
#print axioms hpos_leaf_608

theorem w0_leaf_608 : w0 608 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_774 (F := M)
  rw [hpos_leaf_608] at hs
  calc w0 608 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (608 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (608 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_608

theorem w2_leaf_608 : w2 608 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_774 (F := M)
  rw [hpos_leaf_608] at hs
  calc w2 608 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (608 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (608 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_608

theorem hpos_leaf_609 : order.symm (775 : Fin 1024) = (609 : Fin 1024) := by decide
#print axioms hpos_leaf_609

theorem w0_leaf_609 : w0 609 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_775 (F := M)
  rw [hpos_leaf_609] at hs
  calc w0 609 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (609 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (609 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_609

theorem w2_leaf_609 : w2 609 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_775 (F := M)
  rw [hpos_leaf_609] at hs
  calc w2 609 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (609 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (609 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_609

theorem hpos_leaf_610 : order.symm (790 : Fin 1024) = (610 : Fin 1024) := by decide
#print axioms hpos_leaf_610

theorem w0_leaf_610 : w0 610 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_790 (F := M)
  rw [hpos_leaf_610] at hs
  calc w0 610 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (610 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (610 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_610

theorem w2_leaf_610 : w2 610 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_790 (F := M)
  rw [hpos_leaf_610] at hs
  calc w2 610 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (610 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (610 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_610

theorem hpos_leaf_624 : order.symm (902 : Fin 1024) = (624 : Fin 1024) := by decide
#print axioms hpos_leaf_624

theorem w0_leaf_624 : w0 624 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_902 (F := M)
  rw [hpos_leaf_624] at hs
  calc w0 624 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (624 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (624 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_624

theorem w2_leaf_624 : w2 624 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_902 (F := M)
  rw [hpos_leaf_624] at hs
  calc w2 624 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (624 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (624 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_624

theorem hpos_leaf_625 : order.symm (903 : Fin 1024) = (625 : Fin 1024) := by decide
#print axioms hpos_leaf_625

theorem w0_leaf_625 : w0 625 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_903 (F := M)
  rw [hpos_leaf_625] at hs
  calc w0 625 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (625 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (625 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_625

theorem w2_leaf_625 : w2 625 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_903 (F := M)
  rw [hpos_leaf_625] at hs
  calc w2 625 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (625 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (625 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_625

theorem hpos_leaf_626 : order.symm (918 : Fin 1024) = (626 : Fin 1024) := by decide
#print axioms hpos_leaf_626

theorem w0_leaf_626 : w0 626 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_918 (F := M)
  rw [hpos_leaf_626] at hs
  calc w0 626 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (626 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (626 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_626

theorem w2_leaf_626 : w2 626 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_918 (F := M)
  rw [hpos_leaf_626] at hs
  calc w2 626 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (626 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (626 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_626

theorem hpos_leaf_627 : order.symm (919 : Fin 1024) = (627 : Fin 1024) := by decide
#print axioms hpos_leaf_627

theorem w0_leaf_627 : w0 627 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_919 (F := M)
  rw [hpos_leaf_627] at hs
  calc w0 627 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (627 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (627 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_627

theorem w2_leaf_627 : w2 627 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_919 (F := M)
  rw [hpos_leaf_627] at hs
  calc w2 627 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (627 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (627 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_627

theorem hpos_leaf_628 : order.symm (934 : Fin 1024) = (628 : Fin 1024) := by decide
#print axioms hpos_leaf_628

theorem w0_leaf_628 : w0 628 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_934 (F := M)
  rw [hpos_leaf_628] at hs
  calc w0 628 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (628 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (628 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_628

theorem w2_leaf_628 : w2 628 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_934 (F := M)
  rw [hpos_leaf_628] at hs
  calc w2 628 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (628 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (628 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_628

theorem hpos_leaf_629 : order.symm (935 : Fin 1024) = (629 : Fin 1024) := by decide
#print axioms hpos_leaf_629

theorem w0_leaf_629 : w0 629 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_935 (F := M)
  rw [hpos_leaf_629] at hs
  calc w0 629 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (629 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (629 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_629

theorem w2_leaf_629 : w2 629 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_935 (F := M)
  rw [hpos_leaf_629] at hs
  calc w2 629 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (629 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (629 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_629

theorem hpos_leaf_630 : order.symm (950 : Fin 1024) = (630 : Fin 1024) := by decide
#print axioms hpos_leaf_630

theorem w0_leaf_630 : w0 630 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_950 (F := M)
  rw [hpos_leaf_630] at hs
  calc w0 630 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (630 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (630 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_630

theorem w2_leaf_630 : w2 630 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_950 (F := M)
  rw [hpos_leaf_630] at hs
  calc w2 630 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (630 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (630 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_630

theorem hpos_leaf_631 : order.symm (951 : Fin 1024) = (631 : Fin 1024) := by decide
#print axioms hpos_leaf_631

theorem w0_leaf_631 : w0 631 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_951 (F := M)
  rw [hpos_leaf_631] at hs
  calc w0 631 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (631 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (631 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_631

theorem w2_leaf_631 : w2 631 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_951 (F := M)
  rw [hpos_leaf_631] at hs
  calc w2 631 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (631 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (631 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_631

theorem hpos_leaf_632 : order.symm (966 : Fin 1024) = (632 : Fin 1024) := by decide
#print axioms hpos_leaf_632

theorem w0_leaf_632 : w0 632 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_966 (F := M)
  rw [hpos_leaf_632] at hs
  calc w0 632 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (632 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (632 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_632

theorem w2_leaf_632 : w2 632 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_966 (F := M)
  rw [hpos_leaf_632] at hs
  calc w2 632 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (632 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (632 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_632

theorem hpos_leaf_633 : order.symm (967 : Fin 1024) = (633 : Fin 1024) := by decide
#print axioms hpos_leaf_633

theorem w0_leaf_633 : w0 633 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_967 (F := M)
  rw [hpos_leaf_633] at hs
  calc w0 633 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (633 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (633 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_633

theorem w2_leaf_633 : w2 633 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_967 (F := M)
  rw [hpos_leaf_633] at hs
  calc w2 633 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (633 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (633 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_633

theorem hpos_leaf_634 : order.symm (982 : Fin 1024) = (634 : Fin 1024) := by decide
#print axioms hpos_leaf_634

theorem w0_leaf_634 : w0 634 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_982 (F := M)
  rw [hpos_leaf_634] at hs
  calc w0 634 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (634 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (634 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_634

theorem w2_leaf_634 : w2 634 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_982 (F := M)
  rw [hpos_leaf_634] at hs
  calc w2 634 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (634 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (634 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_634

theorem hpos_leaf_635 : order.symm (983 : Fin 1024) = (635 : Fin 1024) := by decide
#print axioms hpos_leaf_635

theorem w0_leaf_635 : w0 635 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_983 (F := M)
  rw [hpos_leaf_635] at hs
  calc w0 635 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (635 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (635 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_635

theorem w2_leaf_635 : w2 635 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_983 (F := M)
  rw [hpos_leaf_635] at hs
  calc w2 635 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (635 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (635 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_635

theorem hpos_leaf_636 : order.symm (998 : Fin 1024) = (636 : Fin 1024) := by decide
#print axioms hpos_leaf_636

theorem w0_leaf_636 : w0 636 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_998 (F := M)
  rw [hpos_leaf_636] at hs
  calc w0 636 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (636 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (636 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_636

theorem w2_leaf_636 : w2 636 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_998 (F := M)
  rw [hpos_leaf_636] at hs
  calc w2 636 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (636 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (636 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_636

end
end AspisV8R19.R780Point02WeightSharedChunk10
