import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk11
import AspisV8R19.R772Point02DualLeavesChunk22
import AspisV8R19.R772Point02DualLeavesChunk23
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk30
import AspisV8R19.R772Point02DualLeavesChunk31

namespace AspisV8R19.R780Point02WeightSharedChunk11
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_637 : order.symm (999 : Fin 1024) = (637 : Fin 1024) := by decide
#print axioms hpos_leaf_637

theorem w0_leaf_637 : w0 637 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_999 (F := M)
  rw [hpos_leaf_637] at hs
  calc w0 637 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (637 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (637 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_637

theorem w2_leaf_637 : w2 637 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_999 (F := M)
  rw [hpos_leaf_637] at hs
  calc w2 637 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (637 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (637 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_637

theorem hpos_leaf_638 : order.symm (1014 : Fin 1024) = (638 : Fin 1024) := by decide
#print axioms hpos_leaf_638

theorem w0_leaf_638 : w0 638 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1014 (F := M)
  rw [hpos_leaf_638] at hs
  calc w0 638 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (638 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (638 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_638

theorem w2_leaf_638 : w2 638 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1014 (F := M)
  rw [hpos_leaf_638] at hs
  calc w2 638 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (638 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (638 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_638

theorem hpos_leaf_639 : order.symm (1015 : Fin 1024) = (639 : Fin 1024) := by decide
#print axioms hpos_leaf_639

theorem w0_leaf_639 : w0 639 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1015 (F := M)
  rw [hpos_leaf_639] at hs
  calc w0 639 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (639 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (639 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_639

theorem w2_leaf_639 : w2 639 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1015 (F := M)
  rw [hpos_leaf_639] at hs
  calc w2 639 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (639 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (639 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_639

theorem hpos_leaf_640 : order.symm (4 : Fin 1024) = (640 : Fin 1024) := by decide
#print axioms hpos_leaf_640

theorem w0_leaf_640 : w0 640 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_4 (F := M)
  rw [hpos_leaf_640] at hs
  calc w0 640 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (640 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (640 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_640

theorem w2_leaf_640 : w2 640 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_4 (F := M)
  rw [hpos_leaf_640] at hs
  calc w2 640 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (640 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (640 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_640

theorem hpos_leaf_641 : order.symm (5 : Fin 1024) = (641 : Fin 1024) := by decide
#print axioms hpos_leaf_641

theorem w0_leaf_641 : w0 641 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_5 (F := M)
  rw [hpos_leaf_641] at hs
  calc w0 641 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (641 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (641 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_641

theorem w2_leaf_641 : w2 641 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_5 (F := M)
  rw [hpos_leaf_641] at hs
  calc w2 641 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (641 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (641 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_641

theorem hpos_leaf_642 : order.symm (20 : Fin 1024) = (642 : Fin 1024) := by decide
#print axioms hpos_leaf_642

theorem w0_leaf_642 : w0 642 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_20 (F := M)
  rw [hpos_leaf_642] at hs
  calc w0 642 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (642 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (642 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_642

theorem w2_leaf_642 : w2 642 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_20 (F := M)
  rw [hpos_leaf_642] at hs
  calc w2 642 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (642 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (642 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_642

theorem hpos_leaf_704 : order.symm (516 : Fin 1024) = (704 : Fin 1024) := by decide
#print axioms hpos_leaf_704

theorem w0_leaf_704 : w0 704 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_516 (F := M)
  rw [hpos_leaf_704] at hs
  calc w0 704 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (704 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (704 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_704

theorem w2_leaf_704 : w2 704 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_516 (F := M)
  rw [hpos_leaf_704] at hs
  calc w2 704 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (704 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (704 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_704

theorem hpos_leaf_736 : order.symm (772 : Fin 1024) = (736 : Fin 1024) := by decide
#print axioms hpos_leaf_736

theorem w0_leaf_736 : w0 736 = ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_772 (F := M)
  rw [hpos_leaf_736] at hs
  calc w0 736 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (736 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (736 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_736

theorem w2_leaf_736 : w2 736 = ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_772 (F := M)
  rw [hpos_leaf_736] at hs
  calc w2 736 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (736 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (736 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_736

theorem hpos_leaf_752 : order.symm (900 : Fin 1024) = (752 : Fin 1024) := by decide
#print axioms hpos_leaf_752

theorem w0_leaf_752 : w0 752 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_900 (F := M)
  rw [hpos_leaf_752] at hs
  calc w0 752 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (752 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (752 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_752

theorem w2_leaf_752 : w2 752 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_900 (F := M)
  rw [hpos_leaf_752] at hs
  calc w2 752 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (752 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (752 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_752

theorem hpos_leaf_753 : order.symm (901 : Fin 1024) = (753 : Fin 1024) := by decide
#print axioms hpos_leaf_753

theorem w0_leaf_753 : w0 753 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_901 (F := M)
  rw [hpos_leaf_753] at hs
  calc w0 753 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (753 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (753 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_753

theorem w2_leaf_753 : w2 753 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_901 (F := M)
  rw [hpos_leaf_753] at hs
  calc w2 753 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (753 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (753 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_753

theorem hpos_leaf_754 : order.symm (916 : Fin 1024) = (754 : Fin 1024) := by decide
#print axioms hpos_leaf_754

theorem w0_leaf_754 : w0 754 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_916 (F := M)
  rw [hpos_leaf_754] at hs
  calc w0 754 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (754 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (754 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_754

theorem w2_leaf_754 : w2 754 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_916 (F := M)
  rw [hpos_leaf_754] at hs
  calc w2 754 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (754 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (754 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_754

theorem hpos_leaf_755 : order.symm (917 : Fin 1024) = (755 : Fin 1024) := by decide
#print axioms hpos_leaf_755

theorem w0_leaf_755 : w0 755 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_917 (F := M)
  rw [hpos_leaf_755] at hs
  calc w0 755 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (755 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (755 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_755

theorem w2_leaf_755 : w2 755 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_917 (F := M)
  rw [hpos_leaf_755] at hs
  calc w2 755 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (755 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (755 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_755

theorem hpos_leaf_756 : order.symm (932 : Fin 1024) = (756 : Fin 1024) := by decide
#print axioms hpos_leaf_756

theorem w0_leaf_756 : w0 756 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_932 (F := M)
  rw [hpos_leaf_756] at hs
  calc w0 756 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (756 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (756 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_756

theorem w2_leaf_756 : w2 756 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_932 (F := M)
  rw [hpos_leaf_756] at hs
  calc w2 756 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (756 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (756 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_756

theorem hpos_leaf_757 : order.symm (933 : Fin 1024) = (757 : Fin 1024) := by decide
#print axioms hpos_leaf_757

theorem w0_leaf_757 : w0 757 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_933 (F := M)
  rw [hpos_leaf_757] at hs
  calc w0 757 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (757 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (757 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_757

theorem w2_leaf_757 : w2 757 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_933 (F := M)
  rw [hpos_leaf_757] at hs
  calc w2 757 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (757 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (757 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_757

theorem hpos_leaf_758 : order.symm (948 : Fin 1024) = (758 : Fin 1024) := by decide
#print axioms hpos_leaf_758

theorem w0_leaf_758 : w0 758 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_948 (F := M)
  rw [hpos_leaf_758] at hs
  calc w0 758 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (758 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (758 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_758

theorem w2_leaf_758 : w2 758 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_948 (F := M)
  rw [hpos_leaf_758] at hs
  calc w2 758 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (758 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (758 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_758

theorem hpos_leaf_759 : order.symm (949 : Fin 1024) = (759 : Fin 1024) := by decide
#print axioms hpos_leaf_759

theorem w0_leaf_759 : w0 759 = ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_949 (F := M)
  rw [hpos_leaf_759] at hs
  calc w0 759 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (759 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (759 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_759

theorem w2_leaf_759 : w2 759 = ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_949 (F := M)
  rw [hpos_leaf_759] at hs
  calc w2 759 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (759 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (759 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_759

theorem hpos_leaf_760 : order.symm (964 : Fin 1024) = (760 : Fin 1024) := by decide
#print axioms hpos_leaf_760

theorem w0_leaf_760 : w0 760 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_964 (F := M)
  rw [hpos_leaf_760] at hs
  calc w0 760 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (760 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (760 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_760

theorem w2_leaf_760 : w2 760 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_964 (F := M)
  rw [hpos_leaf_760] at hs
  calc w2 760 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (760 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (760 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_760

theorem hpos_leaf_761 : order.symm (965 : Fin 1024) = (761 : Fin 1024) := by decide
#print axioms hpos_leaf_761

theorem w0_leaf_761 : w0 761 = ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_965 (F := M)
  rw [hpos_leaf_761] at hs
  calc w0 761 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (761 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (761 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_761

theorem w2_leaf_761 : w2 761 = ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_965 (F := M)
  rw [hpos_leaf_761] at hs
  calc w2 761 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (761 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (761 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_761

theorem hpos_leaf_762 : order.symm (980 : Fin 1024) = (762 : Fin 1024) := by decide
#print axioms hpos_leaf_762

theorem w0_leaf_762 : w0 762 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_980 (F := M)
  rw [hpos_leaf_762] at hs
  calc w0 762 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (762 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (762 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_762

theorem w2_leaf_762 : w2 762 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_980 (F := M)
  rw [hpos_leaf_762] at hs
  calc w2 762 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (762 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (762 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_762

theorem hpos_leaf_763 : order.symm (981 : Fin 1024) = (763 : Fin 1024) := by decide
#print axioms hpos_leaf_763

theorem w0_leaf_763 : w0 763 = ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_981 (F := M)
  rw [hpos_leaf_763] at hs
  calc w0 763 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (763 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (763 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_763

theorem w2_leaf_763 : w2 763 = ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_981 (F := M)
  rw [hpos_leaf_763] at hs
  calc w2 763 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (763 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (763 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_763

theorem hpos_leaf_764 : order.symm (996 : Fin 1024) = (764 : Fin 1024) := by decide
#print axioms hpos_leaf_764

theorem w0_leaf_764 : w0 764 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_996 (F := M)
  rw [hpos_leaf_764] at hs
  calc w0 764 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (764 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (764 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_764

theorem w2_leaf_764 : w2 764 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_996 (F := M)
  rw [hpos_leaf_764] at hs
  calc w2 764 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (764 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (764 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_764

theorem hpos_leaf_765 : order.symm (997 : Fin 1024) = (765 : Fin 1024) := by decide
#print axioms hpos_leaf_765

theorem w0_leaf_765 : w0 765 = ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_997 (F := M)
  rw [hpos_leaf_765] at hs
  calc w0 765 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (765 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (765 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_765

theorem w2_leaf_765 : w2 765 = ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_997 (F := M)
  rw [hpos_leaf_765] at hs
  calc w2 765 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (765 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (765 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_765

theorem hpos_leaf_766 : order.symm (1012 : Fin 1024) = (766 : Fin 1024) := by decide
#print axioms hpos_leaf_766

theorem w0_leaf_766 : w0 766 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1012 (F := M)
  rw [hpos_leaf_766] at hs
  calc w0 766 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (766 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (766 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_766

theorem w2_leaf_766 : w2 766 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1012 (F := M)
  rw [hpos_leaf_766] at hs
  calc w2 766 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (766 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (766 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_766

theorem hpos_leaf_767 : order.symm (1013 : Fin 1024) = (767 : Fin 1024) := by decide
#print axioms hpos_leaf_767

theorem w0_leaf_767 : w0 767 = ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p0_transport_exact_original_1013 (F := M)
  rw [hpos_leaf_767] at hs
  calc w0 767 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (767 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (767 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_767

theorem w2_leaf_767 : w2 767 = ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk31.p2_transport_exact_original_1013 (F := M)
  rw [hpos_leaf_767] at hs
  calc w2 767 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (767 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (767 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_767

theorem hpos_leaf_768 : order.symm (2 : Fin 1024) = (768 : Fin 1024) := by decide
#print axioms hpos_leaf_768

theorem w0_leaf_768 : w0 768 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_2 (F := M)
  rw [hpos_leaf_768] at hs
  calc w0 768 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (768 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (768 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_768

theorem w2_leaf_768 : w2 768 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_2 (F := M)
  rw [hpos_leaf_768] at hs
  calc w2 768 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (768 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (768 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_768

theorem hpos_leaf_832 : order.symm (514 : Fin 1024) = (832 : Fin 1024) := by decide
#print axioms hpos_leaf_832

theorem w0_leaf_832 : w0 832 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_514 (F := M)
  rw [hpos_leaf_832] at hs
  calc w0 832 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (832 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (832 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_832

theorem w2_leaf_832 : w2 832 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_514 (F := M)
  rw [hpos_leaf_832] at hs
  calc w2 832 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (832 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (832 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_832

theorem hpos_leaf_864 : order.symm (770 : Fin 1024) = (864 : Fin 1024) := by decide
#print axioms hpos_leaf_864

theorem w0_leaf_864 : w0 864 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_770 (F := M)
  rw [hpos_leaf_864] at hs
  calc w0 864 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (864 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (864 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_864

theorem w2_leaf_864 : w2 864 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_770 (F := M)
  rw [hpos_leaf_864] at hs
  calc w2 864 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (864 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (864 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_864

theorem hpos_leaf_880 : order.symm (898 : Fin 1024) = (880 : Fin 1024) := by decide
#print axioms hpos_leaf_880

theorem w0_leaf_880 : w0 880 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_898 (F := M)
  rw [hpos_leaf_880] at hs
  calc w0 880 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (880 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (880 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_880

theorem w2_leaf_880 : w2 880 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_898 (F := M)
  rw [hpos_leaf_880] at hs
  calc w2 880 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (880 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (880 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_880

theorem hpos_leaf_881 : order.symm (899 : Fin 1024) = (881 : Fin 1024) := by decide
#print axioms hpos_leaf_881

theorem w0_leaf_881 : w0 881 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_899 (F := M)
  rw [hpos_leaf_881] at hs
  calc w0 881 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (881 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (881 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_881

theorem w2_leaf_881 : w2 881 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_899 (F := M)
  rw [hpos_leaf_881] at hs
  calc w2 881 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (881 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (881 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_881

theorem hpos_leaf_882 : order.symm (914 : Fin 1024) = (882 : Fin 1024) := by decide
#print axioms hpos_leaf_882

theorem w0_leaf_882 : w0 882 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_914 (F := M)
  rw [hpos_leaf_882] at hs
  calc w0 882 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (882 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (882 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_882

theorem w2_leaf_882 : w2 882 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_914 (F := M)
  rw [hpos_leaf_882] at hs
  calc w2 882 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (882 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (882 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_882

theorem hpos_leaf_883 : order.symm (915 : Fin 1024) = (883 : Fin 1024) := by decide
#print axioms hpos_leaf_883

theorem w0_leaf_883 : w0 883 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p0_transport_zero_original_915 (F := M)
  rw [hpos_leaf_883] at hs
  calc w0 883 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (883 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (883 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_883

theorem w2_leaf_883 : w2 883 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk11.p2_transport_zero_original_915 (F := M)
  rw [hpos_leaf_883] at hs
  calc w2 883 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (883 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (883 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_883

theorem hpos_leaf_884 : order.symm (930 : Fin 1024) = (884 : Fin 1024) := by decide
#print axioms hpos_leaf_884

theorem w0_leaf_884 : w0 884 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_930 (F := M)
  rw [hpos_leaf_884] at hs
  calc w0 884 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (884 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (884 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_884

theorem w2_leaf_884 : w2 884 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_930 (F := M)
  rw [hpos_leaf_884] at hs
  calc w2 884 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (884 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (884 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_884

end
end AspisV8R19.R780Point02WeightSharedChunk11
