import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk12
import AspisV8R19.R772Point02DualLeavesChunk13
import AspisV8R19.R772Point02DualLeavesChunk23
import AspisV8R19.R772Point02DualLeavesChunk24

namespace AspisV8R19.R780Point02WeightSharedChunk12
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_885 : order.symm (931 : Fin 1024) = (885 : Fin 1024) := by decide
#print axioms hpos_leaf_885

theorem w0_leaf_885 : w0 885 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_931 (F := M)
  rw [hpos_leaf_885] at hs
  calc w0 885 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (885 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (885 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_885

theorem w2_leaf_885 : w2 885 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_931 (F := M)
  rw [hpos_leaf_885] at hs
  calc w2 885 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (885 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (885 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_885

theorem hpos_leaf_886 : order.symm (946 : Fin 1024) = (886 : Fin 1024) := by decide
#print axioms hpos_leaf_886

theorem w0_leaf_886 : w0 886 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_946 (F := M)
  rw [hpos_leaf_886] at hs
  calc w0 886 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (886 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (886 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_886

theorem w2_leaf_886 : w2 886 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_946 (F := M)
  rw [hpos_leaf_886] at hs
  calc w2 886 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (886 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (886 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_886

theorem hpos_leaf_887 : order.symm (947 : Fin 1024) = (887 : Fin 1024) := by decide
#print axioms hpos_leaf_887

theorem w0_leaf_887 : w0 887 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_947 (F := M)
  rw [hpos_leaf_887] at hs
  calc w0 887 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (887 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (887 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_887

theorem w2_leaf_887 : w2 887 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_947 (F := M)
  rw [hpos_leaf_887] at hs
  calc w2 887 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (887 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (887 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_887

theorem hpos_leaf_888 : order.symm (962 : Fin 1024) = (888 : Fin 1024) := by decide
#print axioms hpos_leaf_888

theorem w0_leaf_888 : w0 888 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_962 (F := M)
  rw [hpos_leaf_888] at hs
  calc w0 888 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (888 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (888 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_888

theorem w2_leaf_888 : w2 888 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_962 (F := M)
  rw [hpos_leaf_888] at hs
  calc w2 888 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (888 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (888 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_888

theorem hpos_leaf_889 : order.symm (963 : Fin 1024) = (889 : Fin 1024) := by decide
#print axioms hpos_leaf_889

theorem w0_leaf_889 : w0 889 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_963 (F := M)
  rw [hpos_leaf_889] at hs
  calc w0 889 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (889 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (889 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_889

theorem w2_leaf_889 : w2 889 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_963 (F := M)
  rw [hpos_leaf_889] at hs
  calc w2 889 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (889 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (889 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_889

theorem hpos_leaf_890 : order.symm (978 : Fin 1024) = (890 : Fin 1024) := by decide
#print axioms hpos_leaf_890

theorem w0_leaf_890 : w0 890 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_978 (F := M)
  rw [hpos_leaf_890] at hs
  calc w0 890 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (890 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (890 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_890

theorem w2_leaf_890 : w2 890 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_978 (F := M)
  rw [hpos_leaf_890] at hs
  calc w2 890 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (890 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (890 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_890

theorem hpos_leaf_891 : order.symm (979 : Fin 1024) = (891 : Fin 1024) := by decide
#print axioms hpos_leaf_891

theorem w0_leaf_891 : w0 891 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_979 (F := M)
  rw [hpos_leaf_891] at hs
  calc w0 891 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (891 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (891 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_891

theorem w2_leaf_891 : w2 891 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_979 (F := M)
  rw [hpos_leaf_891] at hs
  calc w2 891 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (891 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (891 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_891

theorem hpos_leaf_892 : order.symm (994 : Fin 1024) = (892 : Fin 1024) := by decide
#print axioms hpos_leaf_892

theorem w0_leaf_892 : w0 892 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_994 (F := M)
  rw [hpos_leaf_892] at hs
  calc w0 892 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (892 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (892 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_892

theorem w2_leaf_892 : w2 892 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_994 (F := M)
  rw [hpos_leaf_892] at hs
  calc w2 892 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (892 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (892 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_892

theorem hpos_leaf_893 : order.symm (995 : Fin 1024) = (893 : Fin 1024) := by decide
#print axioms hpos_leaf_893

theorem w0_leaf_893 : w0 893 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_995 (F := M)
  rw [hpos_leaf_893] at hs
  calc w0 893 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (893 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (893 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_893

theorem w2_leaf_893 : w2 893 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_995 (F := M)
  rw [hpos_leaf_893] at hs
  calc w2 893 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (893 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (893 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_893

theorem hpos_leaf_894 : order.symm (1010 : Fin 1024) = (894 : Fin 1024) := by decide
#print axioms hpos_leaf_894

theorem w0_leaf_894 : w0 894 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_1010 (F := M)
  rw [hpos_leaf_894] at hs
  calc w0 894 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (894 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (894 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_894

theorem w2_leaf_894 : w2 894 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_1010 (F := M)
  rw [hpos_leaf_894] at hs
  calc w2 894 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (894 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (894 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_894

theorem hpos_leaf_895 : order.symm (1011 : Fin 1024) = (895 : Fin 1024) := by decide
#print axioms hpos_leaf_895

theorem w0_leaf_895 : w0 895 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_1011 (F := M)
  rw [hpos_leaf_895] at hs
  calc w0 895 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (895 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (895 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_895

theorem w2_leaf_895 : w2 895 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_1011 (F := M)
  rw [hpos_leaf_895] at hs
  calc w2 895 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (895 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (895 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_895

theorem hpos_leaf_896 : order.symm (0 : Fin 1024) = (896 : Fin 1024) := by decide
#print axioms hpos_leaf_896

theorem w0_leaf_896 : w0 896 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_0 (F := M)
  rw [hpos_leaf_896] at hs
  calc w0 896 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (896 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (896 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_896

theorem w2_leaf_896 : w2 896 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_0 (F := M)
  rw [hpos_leaf_896] at hs
  calc w2 896 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (896 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (896 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_896

theorem hpos_leaf_900 : order.symm (32 : Fin 1024) = (900 : Fin 1024) := by decide
#print axioms hpos_leaf_900

theorem w0_leaf_900 : w0 900 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_32 (F := M)
  rw [hpos_leaf_900] at hs
  calc w0 900 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (900 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (900 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_900

theorem w2_leaf_900 : w2 900 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_32 (F := M)
  rw [hpos_leaf_900] at hs
  calc w2 900 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (900 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (900 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_900

theorem hpos_leaf_901 : order.symm (33 : Fin 1024) = (901 : Fin 1024) := by decide
#print axioms hpos_leaf_901

theorem w0_leaf_901 : w0 901 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_33 (F := M)
  rw [hpos_leaf_901] at hs
  calc w0 901 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (901 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (901 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_901

theorem w2_leaf_901 : w2 901 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_33 (F := M)
  rw [hpos_leaf_901] at hs
  calc w2 901 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (901 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (901 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_901

theorem hpos_leaf_902 : order.symm (48 : Fin 1024) = (902 : Fin 1024) := by decide
#print axioms hpos_leaf_902

theorem w0_leaf_902 : w0 902 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_48 (F := M)
  rw [hpos_leaf_902] at hs
  calc w0 902 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (902 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (902 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_902

theorem w2_leaf_902 : w2 902 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_48 (F := M)
  rw [hpos_leaf_902] at hs
  calc w2 902 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (902 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (902 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_902

theorem hpos_leaf_903 : order.symm (49 : Fin 1024) = (903 : Fin 1024) := by decide
#print axioms hpos_leaf_903

theorem w0_leaf_903 : w0 903 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_49 (F := M)
  rw [hpos_leaf_903] at hs
  calc w0 903 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (903 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (903 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_903

theorem w2_leaf_903 : w2 903 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_49 (F := M)
  rw [hpos_leaf_903] at hs
  calc w2 903 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (903 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (903 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_903

theorem hpos_leaf_904 : order.symm (64 : Fin 1024) = (904 : Fin 1024) := by decide
#print axioms hpos_leaf_904

theorem w0_leaf_904 : w0 904 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_64 (F := M)
  rw [hpos_leaf_904] at hs
  calc w0 904 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (904 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (904 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_904

theorem w2_leaf_904 : w2 904 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_64 (F := M)
  rw [hpos_leaf_904] at hs
  calc w2 904 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (904 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (904 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_904

theorem hpos_leaf_905 : order.symm (65 : Fin 1024) = (905 : Fin 1024) := by decide
#print axioms hpos_leaf_905

theorem w0_leaf_905 : w0 905 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_65 (F := M)
  rw [hpos_leaf_905] at hs
  calc w0 905 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (905 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (905 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_905

theorem w2_leaf_905 : w2 905 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_65 (F := M)
  rw [hpos_leaf_905] at hs
  calc w2 905 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (905 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (905 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_905

theorem hpos_leaf_906 : order.symm (80 : Fin 1024) = (906 : Fin 1024) := by decide
#print axioms hpos_leaf_906

theorem w0_leaf_906 : w0 906 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_80 (F := M)
  rw [hpos_leaf_906] at hs
  calc w0 906 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (906 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (906 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_906

theorem w2_leaf_906 : w2 906 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_80 (F := M)
  rw [hpos_leaf_906] at hs
  calc w2 906 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (906 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (906 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_906

theorem hpos_leaf_907 : order.symm (81 : Fin 1024) = (907 : Fin 1024) := by decide
#print axioms hpos_leaf_907

theorem w0_leaf_907 : w0 907 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_81 (F := M)
  rw [hpos_leaf_907] at hs
  calc w0 907 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (907 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (907 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_907

theorem w2_leaf_907 : w2 907 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_81 (F := M)
  rw [hpos_leaf_907] at hs
  calc w2 907 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (907 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (907 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_907

theorem hpos_leaf_908 : order.symm (96 : Fin 1024) = (908 : Fin 1024) := by decide
#print axioms hpos_leaf_908

theorem w0_leaf_908 : w0 908 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_96 (F := M)
  rw [hpos_leaf_908] at hs
  calc w0 908 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (908 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (908 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_908

theorem w2_leaf_908 : w2 908 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_96 (F := M)
  rw [hpos_leaf_908] at hs
  calc w2 908 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (908 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (908 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_908

theorem hpos_leaf_909 : order.symm (97 : Fin 1024) = (909 : Fin 1024) := by decide
#print axioms hpos_leaf_909

theorem w0_leaf_909 : w0 909 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_97 (F := M)
  rw [hpos_leaf_909] at hs
  calc w0 909 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (909 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (909 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_909

theorem w2_leaf_909 : w2 909 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_97 (F := M)
  rw [hpos_leaf_909] at hs
  calc w2 909 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (909 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (909 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_909

theorem hpos_leaf_910 : order.symm (112 : Fin 1024) = (910 : Fin 1024) := by decide
#print axioms hpos_leaf_910

theorem w0_leaf_910 : w0 910 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_112 (F := M)
  rw [hpos_leaf_910] at hs
  calc w0 910 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (910 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (910 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_910

theorem w2_leaf_910 : w2 910 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_112 (F := M)
  rw [hpos_leaf_910] at hs
  calc w2 910 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (910 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (910 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_910

theorem hpos_leaf_911 : order.symm (113 : Fin 1024) = (911 : Fin 1024) := by decide
#print axioms hpos_leaf_911

theorem w0_leaf_911 : w0 911 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_113 (F := M)
  rw [hpos_leaf_911] at hs
  calc w0 911 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (911 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (911 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_911

theorem w2_leaf_911 : w2 911 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_113 (F := M)
  rw [hpos_leaf_911] at hs
  calc w2 911 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (911 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (911 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_911

theorem hpos_leaf_912 : order.symm (128 : Fin 1024) = (912 : Fin 1024) := by decide
#print axioms hpos_leaf_912

theorem w0_leaf_912 : w0 912 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_128 (F := M)
  rw [hpos_leaf_912] at hs
  calc w0 912 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (912 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (912 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_912

theorem w2_leaf_912 : w2 912 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_128 (F := M)
  rw [hpos_leaf_912] at hs
  calc w2 912 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (912 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (912 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_912

theorem hpos_leaf_913 : order.symm (129 : Fin 1024) = (913 : Fin 1024) := by decide
#print axioms hpos_leaf_913

theorem w0_leaf_913 : w0 913 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_129 (F := M)
  rw [hpos_leaf_913] at hs
  calc w0 913 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (913 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (913 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_913

theorem w2_leaf_913 : w2 913 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_129 (F := M)
  rw [hpos_leaf_913] at hs
  calc w2 913 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (913 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (913 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_913

theorem hpos_leaf_914 : order.symm (144 : Fin 1024) = (914 : Fin 1024) := by decide
#print axioms hpos_leaf_914

theorem w0_leaf_914 : w0 914 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_144 (F := M)
  rw [hpos_leaf_914] at hs
  calc w0 914 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (914 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (914 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_914

theorem w2_leaf_914 : w2 914 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_144 (F := M)
  rw [hpos_leaf_914] at hs
  calc w2 914 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (914 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (914 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_914

theorem hpos_leaf_915 : order.symm (145 : Fin 1024) = (915 : Fin 1024) := by decide
#print axioms hpos_leaf_915

theorem w0_leaf_915 : w0 915 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_145 (F := M)
  rw [hpos_leaf_915] at hs
  calc w0 915 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (915 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (915 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_915

theorem w2_leaf_915 : w2 915 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_145 (F := M)
  rw [hpos_leaf_915] at hs
  calc w2 915 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (915 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (915 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_915

theorem hpos_leaf_916 : order.symm (160 : Fin 1024) = (916 : Fin 1024) := by decide
#print axioms hpos_leaf_916

theorem w0_leaf_916 : w0 916 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p0_transport_zero_original_160 (F := M)
  rw [hpos_leaf_916] at hs
  calc w0 916 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (916 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (916 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_916

theorem w2_leaf_916 : w2 916 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk23.p2_transport_zero_original_160 (F := M)
  rw [hpos_leaf_916] at hs
  calc w2 916 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (916 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (916 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_916

theorem hpos_leaf_917 : order.symm (161 : Fin 1024) = (917 : Fin 1024) := by decide
#print axioms hpos_leaf_917

theorem w0_leaf_917 : w0 917 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p0_transport_zero_original_161 (F := M)
  rw [hpos_leaf_917] at hs
  calc w0 917 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (917 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (917 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_917

theorem w2_leaf_917 : w2 917 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk12.p2_transport_zero_original_161 (F := M)
  rw [hpos_leaf_917] at hs
  calc w2 917 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (917 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (917 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_917

theorem hpos_leaf_918 : order.symm (176 : Fin 1024) = (918 : Fin 1024) := by decide
#print axioms hpos_leaf_918

theorem w0_leaf_918 : w0 918 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_176 (F := M)
  rw [hpos_leaf_918] at hs
  calc w0 918 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (918 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (918 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_918

theorem w2_leaf_918 : w2 918 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_176 (F := M)
  rw [hpos_leaf_918] at hs
  calc w2 918 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (918 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (918 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_918

theorem hpos_leaf_919 : order.symm (177 : Fin 1024) = (919 : Fin 1024) := by decide
#print axioms hpos_leaf_919

theorem w0_leaf_919 : w0 919 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_177 (F := M)
  rw [hpos_leaf_919] at hs
  calc w0 919 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (919 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (919 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_919

theorem w2_leaf_919 : w2 919 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_177 (F := M)
  rw [hpos_leaf_919] at hs
  calc w2 919 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (919 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (919 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_919

end
end AspisV8R19.R780Point02WeightSharedChunk12
