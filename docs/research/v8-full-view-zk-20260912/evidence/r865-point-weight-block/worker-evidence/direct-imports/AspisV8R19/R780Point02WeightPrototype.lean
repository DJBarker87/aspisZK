import AspisV8R19.R740SparsePointObservation
import AspisV8R19.R748SchedulePrototype
import AspisV8R19.R771Point02Transport
import AspisV8R19.R772Point02DualLeavesChunk00
import AspisV8R19.R772Point02DualLeavesChunk05
import AspisV8R19.R772Point02DualLeavesChunk10
import AspisV8R19.R772Point02DualLeavesChunk18
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk30

namespace AspisV8R19.R780Point02WeightPrototype
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R740SparsePointObservation
open AspisV8R19.R748SchedulePrototype
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096

abbrev M := ZMod 2147483647
def half : M := 1073741824
abbrev point0 : Fin 10 → M := AspisV8R19.R771Point02Transport.point0 (F := M)
abbrev point2 : Fin 10 → M := AspisV8R19.R771Point02Transport.point2 (F := M)
def w0 (i : Nat) : M := extendFin1024 (transportDual inactive (1023 : Fin 1024) order (fun j => sourcePointBasis point0 j.val)) i
def w2 (i : Nat) : M := extendFin1024 (transportDual inactive (1023 : Fin 1024) order (fun j => sourcePointBasis point2 j.val)) i
def pw0 : Nat → M := pointWeight half 7 5 (-5) point0
def pw2 : Nat → M := pointWeight half 7 5 (-5) point2

def p0b777 : M := ([1, 1, -1, -2, -3, -1, 2, -2, 1, 2] : List M).prod
def p0b792 : M := ([1, 1, -1, -2, -3, 2, 2, -2, 1, -1] : List M).prod
def p0b905 : M := ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod
def p0b920 : M := ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod
def p0b969 : M := ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod
def p0b984 : M := ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod
def p0b1001 : M := ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod
def p0b1016 : M := ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod
def p0b1017 : M := ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod
def p2b777 : M := ([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List M).prod
def p2b792 : M := ([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List M).prod
def p2b905 : M := ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod
def p2b920 : M := ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod
def p2b969 : M := ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod
def p2b984 : M := ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod
def p2b1001 : M := ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod
def p2b1016 : M := ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod
def p2b1017 : M := ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod

private theorem w0_510 : w0 510 = p0b1016 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (510 : Fin 1024) = p0b1016
  have hpos : order.symm (1016 : Fin 1024) = (510 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_1016 (F := M)

private theorem w0_506 : w0 506 = p0b984 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (506 : Fin 1024) = p0b984
  have hpos : order.symm (984 : Fin 1024) = (506 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_984 (F := M)

private theorem w0_498 : w0 498 = p0b920 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (498 : Fin 1024) = p0b920
  have hpos : order.symm (920 : Fin 1024) = (498 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_920 (F := M)

private theorem w0_482 : w0 482 = p0b792 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (482 : Fin 1024) = p0b792
  have hpos : order.symm (792 : Fin 1024) = (482 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_792 (F := M)

private theorem w0_450 : w0 450 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (450 : Fin 1024) = 0
  have hpos : order.symm (536 : Fin 1024) = (450 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_536 (F := M)

private theorem w0_386 : w0 386 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (386 : Fin 1024) = 0
  have hpos : order.symm (24 : Fin 1024) = (386 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_24 (F := M)

private theorem w0_258 : w0 258 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (258 : Fin 1024) = 0
  have hpos : order.symm (26 : Fin 1024) = (258 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_26 (F := M)

private theorem w0_2 : w0 2 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (2 : Fin 1024) = 0
  have hpos : order.symm (30 : Fin 1024) = (2 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_30 (F := M)

private theorem w0_514 : w0 514 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (514 : Fin 1024) = 0
  have hpos : order.symm (22 : Fin 1024) = (514 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_22 (F := M)

private theorem w0_511 : w0 511 = p0b1017 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (511 : Fin 1024) = p0b1017
  have hpos : order.symm (1017 : Fin 1024) = (511 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1017 (F := M)

private theorem w0_509 : w0 509 = p0b1001 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (509 : Fin 1024) = p0b1001
  have hpos : order.symm (1001 : Fin 1024) = (509 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1001 (F := M)

private theorem w0_505 : w0 505 = p0b969 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (505 : Fin 1024) = p0b969
  have hpos : order.symm (969 : Fin 1024) = (505 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_969 (F := M)

private theorem w0_497 : w0 497 = p0b905 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (497 : Fin 1024) = p0b905
  have hpos : order.symm (905 : Fin 1024) = (497 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_905 (F := M)

private theorem w0_481 : w0 481 = p0b777 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (481 : Fin 1024) = p0b777
  have hpos : order.symm (777 : Fin 1024) = (481 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_777 (F := M)

private theorem w0_449 : w0 449 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (449 : Fin 1024) = 0
  have hpos : order.symm (521 : Fin 1024) = (449 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_521 (F := M)

private theorem w0_385 : w0 385 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (385 : Fin 1024) = 0
  have hpos : order.symm (9 : Fin 1024) = (385 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_9 (F := M)

private theorem w0_257 : w0 257 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (257 : Fin 1024) = 0
  have hpos : order.symm (11 : Fin 1024) = (257 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_11 (F := M)

private theorem w0_1 : w0 1 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (1 : Fin 1024) = 0
  have hpos : order.symm (15 : Fin 1024) = (1 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk00.p0_transport_zero_original_15 (F := M)

private theorem w0_513 : w0 513 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point0 j.val) (513 : Fin 1024) = 0
  have hpos : order.symm (7 : Fin 1024) = (513 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_7 (F := M)

private theorem w2_510 : w2 510 = p2b1016 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (510 : Fin 1024) = p2b1016
  have hpos : order.symm (1016 : Fin 1024) = (510 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_1016 (F := M)

private theorem w2_506 : w2 506 = p2b984 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (506 : Fin 1024) = p2b984
  have hpos : order.symm (984 : Fin 1024) = (506 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_984 (F := M)

private theorem w2_498 : w2 498 = p2b920 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (498 : Fin 1024) = p2b920
  have hpos : order.symm (920 : Fin 1024) = (498 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_920 (F := M)

private theorem w2_482 : w2 482 = p2b792 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (482 : Fin 1024) = p2b792
  have hpos : order.symm (792 : Fin 1024) = (482 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_792 (F := M)

private theorem w2_450 : w2 450 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (450 : Fin 1024) = 0
  have hpos : order.symm (536 : Fin 1024) = (450 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_536 (F := M)

private theorem w2_386 : w2 386 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (386 : Fin 1024) = 0
  have hpos : order.symm (24 : Fin 1024) = (386 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_24 (F := M)

private theorem w2_258 : w2 258 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (258 : Fin 1024) = 0
  have hpos : order.symm (26 : Fin 1024) = (258 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_26 (F := M)

private theorem w2_2 : w2 2 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (2 : Fin 1024) = 0
  have hpos : order.symm (30 : Fin 1024) = (2 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_30 (F := M)

private theorem w2_514 : w2 514 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (514 : Fin 1024) = 0
  have hpos : order.symm (22 : Fin 1024) = (514 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_22 (F := M)

private theorem w2_511 : w2 511 = p2b1017 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (511 : Fin 1024) = p2b1017
  have hpos : order.symm (1017 : Fin 1024) = (511 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1017 (F := M)

private theorem w2_509 : w2 509 = p2b1001 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (509 : Fin 1024) = p2b1001
  have hpos : order.symm (1001 : Fin 1024) = (509 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1001 (F := M)

private theorem w2_505 : w2 505 = p2b969 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (505 : Fin 1024) = p2b969
  have hpos : order.symm (969 : Fin 1024) = (505 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_969 (F := M)

private theorem w2_497 : w2 497 = p2b905 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (497 : Fin 1024) = p2b905
  have hpos : order.symm (905 : Fin 1024) = (497 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_905 (F := M)

private theorem w2_481 : w2 481 = p2b777 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (481 : Fin 1024) = p2b777
  have hpos : order.symm (777 : Fin 1024) = (481 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_777 (F := M)

private theorem w2_449 : w2 449 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (449 : Fin 1024) = 0
  have hpos : order.symm (521 : Fin 1024) = (449 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_521 (F := M)

private theorem w2_385 : w2 385 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (385 : Fin 1024) = 0
  have hpos : order.symm (9 : Fin 1024) = (385 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_9 (F := M)

private theorem w2_257 : w2 257 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (257 : Fin 1024) = 0
  have hpos : order.symm (11 : Fin 1024) = (257 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_11 (F := M)

private theorem w2_1 : w2 1 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (1 : Fin 1024) = 0
  have hpos : order.symm (15 : Fin 1024) = (1 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk00.p2_transport_zero_original_15 (F := M)

private theorem w2_513 : w2 513 = 0 := by
  change AspisV8R16.transportDual inactive (1023 : Fin 1024) order
    (fun j : Fin 1024 => sourcePointBasis point2 j.val) (513 : Fin 1024) = 0
  have hpos : order.symm (7 : Fin 1024) = (513 : Fin 1024) := by decide
  rw [← hpos]
  exact AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_7 (F := M)

private theorem pw0_511_gather : pw0 511 =
    -5 * (w0 510 - (half*w0 510 + half^2*w0 506 + half^3*w0 498 + half^4*w0 482 + half^5*w0 450 + half^6*w0 386 + half^7*w0 258 + half^8*w0 2 + half^8*w0 514)) +
      7*w0 511 + 5*(half*w0 509 + half^2*w0 505 + half^3*w0 497 + half^4*w0 481 + half^5*w0 449 + half^6*w0 385 + half^7*w0 257 + half^8*w0 1 + half^8*w0 513) := by
  change sourceChordTranspose half w0 7 5 (-5) 511 = _
  change chordDualOdd half (zeroExtend 512 (fun i => w0 (2*i))) (zeroExtend 512 (fun i => w0 (2*i+1))) 7 5 (-5) 255 = _
  unfold chordDualOdd
  rw [gatherGather255, gather255]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i)) i = w0 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w0 (2*i+1)) i = w0 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [hwe 255 (by omega), hwe 253 (by omega), hwe 249 (by omega), hwe 241 (by omega), hwe 225 (by omega), hwe 193 (by omega), hwe 129 (by omega), hwe 1 (by omega), hwe 257 (by omega),
    hwo 255 (by omega), hwo 254 (by omega), hwo 252 (by omega), hwo 248 (by omega), hwo 240 (by omega), hwo 224 (by omega), hwo 192 (by omega), hwo 128 (by omega), hwo 0 (by omega), hwo 256 (by omega)]

private theorem pw2_511_gather : pw2 511 =
    -5 * (w2 510 - (half*w2 510 + half^2*w2 506 + half^3*w2 498 + half^4*w2 482 + half^5*w2 450 + half^6*w2 386 + half^7*w2 258 + half^8*w2 2 + half^8*w2 514)) +
      7*w2 511 + 5*(half*w2 509 + half^2*w2 505 + half^3*w2 497 + half^4*w2 481 + half^5*w2 449 + half^6*w2 385 + half^7*w2 257 + half^8*w2 1 + half^8*w2 513) := by
  change sourceChordTranspose half w2 7 5 (-5) 511 = _
  change chordDualOdd half (zeroExtend 512 (fun i => w2 (2*i))) (zeroExtend 512 (fun i => w2 (2*i+1))) 7 5 (-5) 255 = _
  unfold chordDualOdd
  rw [gatherGather255, gather255]
  have hwe (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i)) i = w2 (2*i) := by
    unfold zeroExtend; rw [if_pos hi]
  have hwo (i : Nat) (hi : i < 512) : zeroExtend 512 (fun i => w2 (2*i+1)) i = w2 (2*i+1) := by
    unfold zeroExtend; rw [if_pos hi]
  rw [hwe 255 (by omega), hwe 253 (by omega), hwe 249 (by omega), hwe 241 (by omega), hwe 225 (by omega), hwe 193 (by omega), hwe 129 (by omega), hwe 1 (by omega), hwe 257 (by omega),
    hwo 255 (by omega), hwo 254 (by omega), hwo 252 (by omega), hwo 248 (by omega), hwo 240 (by omega), hwo 224 (by omega), hwo 192 (by omega), hwo 128 (by omega), hwo 0 (by omega), hwo 256 (by omega)]

theorem p0_weight_511_exact : pw0 511 = -5 * (p0b1016 - (half*p0b1016 + half^2*p0b984 + half^3*p0b920 + half^4*p0b792 + half^5*0 + half^6*0 + half^7*0 + half^8*0 + half^8*0)) + 7*p0b1017 + 5*(half*p0b1001 + half^2*p0b969 + half^3*p0b905 + half^4*p0b777 + half^5*0 + half^6*0 + half^7*0 + half^8*0 + half^8*0) := by
  rw [pw0_511_gather]
  simp only [w0_510, w0_506, w0_498, w0_482, w0_450, w0_386, w0_258, w0_2, w0_514, w0_511, w0_509, w0_505, w0_497, w0_481, w0_449, w0_385, w0_257, w0_1, w0_513]
#print axioms p0_weight_511_exact

theorem p2_weight_511_exact : pw2 511 = -5 * (p2b1016 - (half*p2b1016 + half^2*p2b984 + half^3*p2b920 + half^4*p2b792 + half^5*0 + half^6*0 + half^7*0 + half^8*0 + half^8*0)) + 7*p2b1017 + 5*(half*p2b1001 + half^2*p2b969 + half^3*p2b905 + half^4*p2b777 + half^5*0 + half^6*0 + half^7*0 + half^8*0 + half^8*0) := by
  rw [pw2_511_gather]
  simp only [w2_510, w2_506, w2_498, w2_482, w2_450, w2_386, w2_258, w2_2, w2_514, w2_511, w2_509, w2_505, w2_497, w2_481, w2_449, w2_385, w2_257, w2_1, w2_513]
#print axioms p2_weight_511_exact

end
end AspisV8R19.R780Point02WeightPrototype
