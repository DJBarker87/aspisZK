import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk13
import AspisV8R19.R772Point02DualLeavesChunk14
import AspisV8R19.R772Point02DualLeavesChunk24

namespace AspisV8R19.R780Point02WeightSharedChunk13
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_920 : order.symm (192 : Fin 1024) = (920 : Fin 1024) := by decide
#print axioms hpos_leaf_920

theorem w0_leaf_920 : w0 920 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_192 (F := M)
  rw [hpos_leaf_920] at hs
  calc w0 920 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (920 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (920 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_920

theorem w2_leaf_920 : w2 920 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_192 (F := M)
  rw [hpos_leaf_920] at hs
  calc w2 920 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (920 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (920 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_920

theorem hpos_leaf_921 : order.symm (193 : Fin 1024) = (921 : Fin 1024) := by decide
#print axioms hpos_leaf_921

theorem w0_leaf_921 : w0 921 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_193 (F := M)
  rw [hpos_leaf_921] at hs
  calc w0 921 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (921 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (921 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_921

theorem w2_leaf_921 : w2 921 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_193 (F := M)
  rw [hpos_leaf_921] at hs
  calc w2 921 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (921 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (921 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_921

theorem hpos_leaf_922 : order.symm (208 : Fin 1024) = (922 : Fin 1024) := by decide
#print axioms hpos_leaf_922

theorem w0_leaf_922 : w0 922 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_208 (F := M)
  rw [hpos_leaf_922] at hs
  calc w0 922 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (922 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (922 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_922

theorem w2_leaf_922 : w2 922 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_208 (F := M)
  rw [hpos_leaf_922] at hs
  calc w2 922 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (922 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (922 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_922

theorem hpos_leaf_923 : order.symm (209 : Fin 1024) = (923 : Fin 1024) := by decide
#print axioms hpos_leaf_923

theorem w0_leaf_923 : w0 923 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_209 (F := M)
  rw [hpos_leaf_923] at hs
  calc w0 923 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (923 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (923 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_923

theorem w2_leaf_923 : w2 923 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_209 (F := M)
  rw [hpos_leaf_923] at hs
  calc w2 923 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (923 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (923 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_923

theorem hpos_leaf_924 : order.symm (224 : Fin 1024) = (924 : Fin 1024) := by decide
#print axioms hpos_leaf_924

theorem w0_leaf_924 : w0 924 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_224 (F := M)
  rw [hpos_leaf_924] at hs
  calc w0 924 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (924 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (924 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_924

theorem w2_leaf_924 : w2 924 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_224 (F := M)
  rw [hpos_leaf_924] at hs
  calc w2 924 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (924 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (924 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_924

theorem hpos_leaf_925 : order.symm (225 : Fin 1024) = (925 : Fin 1024) := by decide
#print axioms hpos_leaf_925

theorem w0_leaf_925 : w0 925 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_225 (F := M)
  rw [hpos_leaf_925] at hs
  calc w0 925 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (925 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (925 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_925

theorem w2_leaf_925 : w2 925 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_225 (F := M)
  rw [hpos_leaf_925] at hs
  calc w2 925 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (925 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (925 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_925

theorem hpos_leaf_926 : order.symm (240 : Fin 1024) = (926 : Fin 1024) := by decide
#print axioms hpos_leaf_926

theorem w0_leaf_926 : w0 926 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_240 (F := M)
  rw [hpos_leaf_926] at hs
  calc w0 926 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (926 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (926 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_926

theorem w2_leaf_926 : w2 926 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_240 (F := M)
  rw [hpos_leaf_926] at hs
  calc w2 926 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (926 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (926 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_926

theorem hpos_leaf_927 : order.symm (241 : Fin 1024) = (927 : Fin 1024) := by decide
#print axioms hpos_leaf_927

theorem w0_leaf_927 : w0 927 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_241 (F := M)
  rw [hpos_leaf_927] at hs
  calc w0 927 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (927 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (927 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_927

theorem w2_leaf_927 : w2 927 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_241 (F := M)
  rw [hpos_leaf_927] at hs
  calc w2 927 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (927 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (927 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_927

theorem hpos_leaf_928 : order.symm (256 : Fin 1024) = (928 : Fin 1024) := by decide
#print axioms hpos_leaf_928

theorem w0_leaf_928 : w0 928 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_256 (F := M)
  rw [hpos_leaf_928] at hs
  calc w0 928 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (928 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (928 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_928

theorem w2_leaf_928 : w2 928 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_256 (F := M)
  rw [hpos_leaf_928] at hs
  calc w2 928 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (928 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (928 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_928

theorem hpos_leaf_929 : order.symm (257 : Fin 1024) = (929 : Fin 1024) := by decide
#print axioms hpos_leaf_929

theorem w0_leaf_929 : w0 929 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_257 (F := M)
  rw [hpos_leaf_929] at hs
  calc w0 929 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (929 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (929 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_929

theorem w2_leaf_929 : w2 929 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_257 (F := M)
  rw [hpos_leaf_929] at hs
  calc w2 929 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (929 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (929 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_929

theorem hpos_leaf_930 : order.symm (272 : Fin 1024) = (930 : Fin 1024) := by decide
#print axioms hpos_leaf_930

theorem w0_leaf_930 : w0 930 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_272 (F := M)
  rw [hpos_leaf_930] at hs
  calc w0 930 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (930 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (930 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_930

theorem w2_leaf_930 : w2 930 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_272 (F := M)
  rw [hpos_leaf_930] at hs
  calc w2 930 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (930 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (930 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_930

theorem hpos_leaf_931 : order.symm (273 : Fin 1024) = (931 : Fin 1024) := by decide
#print axioms hpos_leaf_931

theorem w0_leaf_931 : w0 931 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_273 (F := M)
  rw [hpos_leaf_931] at hs
  calc w0 931 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (931 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (931 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_931

theorem w2_leaf_931 : w2 931 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_273 (F := M)
  rw [hpos_leaf_931] at hs
  calc w2 931 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (931 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (931 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_931

theorem hpos_leaf_932 : order.symm (288 : Fin 1024) = (932 : Fin 1024) := by decide
#print axioms hpos_leaf_932

theorem w0_leaf_932 : w0 932 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_288 (F := M)
  rw [hpos_leaf_932] at hs
  calc w0 932 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (932 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (932 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_932

theorem w2_leaf_932 : w2 932 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_288 (F := M)
  rw [hpos_leaf_932] at hs
  calc w2 932 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (932 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (932 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_932

theorem hpos_leaf_933 : order.symm (289 : Fin 1024) = (933 : Fin 1024) := by decide
#print axioms hpos_leaf_933

theorem w0_leaf_933 : w0 933 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_289 (F := M)
  rw [hpos_leaf_933] at hs
  calc w0 933 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (933 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (933 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_933

theorem w2_leaf_933 : w2 933 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_289 (F := M)
  rw [hpos_leaf_933] at hs
  calc w2 933 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (933 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (933 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_933

theorem hpos_leaf_934 : order.symm (304 : Fin 1024) = (934 : Fin 1024) := by decide
#print axioms hpos_leaf_934

theorem w0_leaf_934 : w0 934 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_304 (F := M)
  rw [hpos_leaf_934] at hs
  calc w0 934 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (934 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (934 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_934

theorem w2_leaf_934 : w2 934 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_304 (F := M)
  rw [hpos_leaf_934] at hs
  calc w2 934 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (934 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (934 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_934

theorem hpos_leaf_935 : order.symm (305 : Fin 1024) = (935 : Fin 1024) := by decide
#print axioms hpos_leaf_935

theorem w0_leaf_935 : w0 935 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_305 (F := M)
  rw [hpos_leaf_935] at hs
  calc w0 935 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (935 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (935 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_935

theorem w2_leaf_935 : w2 935 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_305 (F := M)
  rw [hpos_leaf_935] at hs
  calc w2 935 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (935 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (935 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_935

theorem hpos_leaf_936 : order.symm (320 : Fin 1024) = (936 : Fin 1024) := by decide
#print axioms hpos_leaf_936

theorem w0_leaf_936 : w0 936 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_320 (F := M)
  rw [hpos_leaf_936] at hs
  calc w0 936 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (936 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (936 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_936

theorem w2_leaf_936 : w2 936 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_320 (F := M)
  rw [hpos_leaf_936] at hs
  calc w2 936 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (936 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (936 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_936

theorem hpos_leaf_937 : order.symm (321 : Fin 1024) = (937 : Fin 1024) := by decide
#print axioms hpos_leaf_937

theorem w0_leaf_937 : w0 937 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_321 (F := M)
  rw [hpos_leaf_937] at hs
  calc w0 937 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (937 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (937 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_937

theorem w2_leaf_937 : w2 937 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_321 (F := M)
  rw [hpos_leaf_937] at hs
  calc w2 937 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (937 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (937 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_937

theorem hpos_leaf_938 : order.symm (336 : Fin 1024) = (938 : Fin 1024) := by decide
#print axioms hpos_leaf_938

theorem w0_leaf_938 : w0 938 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_336 (F := M)
  rw [hpos_leaf_938] at hs
  calc w0 938 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (938 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (938 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_938

theorem w2_leaf_938 : w2 938 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_336 (F := M)
  rw [hpos_leaf_938] at hs
  calc w2 938 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (938 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (938 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_938

theorem hpos_leaf_939 : order.symm (337 : Fin 1024) = (939 : Fin 1024) := by decide
#print axioms hpos_leaf_939

theorem w0_leaf_939 : w0 939 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_337 (F := M)
  rw [hpos_leaf_939] at hs
  calc w0 939 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (939 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (939 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_939

theorem w2_leaf_939 : w2 939 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_337 (F := M)
  rw [hpos_leaf_939] at hs
  calc w2 939 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (939 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (939 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_939

theorem hpos_leaf_940 : order.symm (352 : Fin 1024) = (940 : Fin 1024) := by decide
#print axioms hpos_leaf_940

theorem w0_leaf_940 : w0 940 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_352 (F := M)
  rw [hpos_leaf_940] at hs
  calc w0 940 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (940 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (940 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_940

theorem w2_leaf_940 : w2 940 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_352 (F := M)
  rw [hpos_leaf_940] at hs
  calc w2 940 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (940 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (940 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_940

theorem hpos_leaf_941 : order.symm (353 : Fin 1024) = (941 : Fin 1024) := by decide
#print axioms hpos_leaf_941

theorem w0_leaf_941 : w0 941 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_353 (F := M)
  rw [hpos_leaf_941] at hs
  calc w0 941 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (941 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (941 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_941

theorem w2_leaf_941 : w2 941 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_353 (F := M)
  rw [hpos_leaf_941] at hs
  calc w2 941 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (941 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (941 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_941

theorem hpos_leaf_942 : order.symm (368 : Fin 1024) = (942 : Fin 1024) := by decide
#print axioms hpos_leaf_942

theorem w0_leaf_942 : w0 942 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_368 (F := M)
  rw [hpos_leaf_942] at hs
  calc w0 942 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (942 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (942 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_942

theorem w2_leaf_942 : w2 942 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_368 (F := M)
  rw [hpos_leaf_942] at hs
  calc w2 942 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (942 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (942 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_942

theorem hpos_leaf_943 : order.symm (369 : Fin 1024) = (943 : Fin 1024) := by decide
#print axioms hpos_leaf_943

theorem w0_leaf_943 : w0 943 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_369 (F := M)
  rw [hpos_leaf_943] at hs
  calc w0 943 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (943 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (943 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_943

theorem w2_leaf_943 : w2 943 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_369 (F := M)
  rw [hpos_leaf_943] at hs
  calc w2 943 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (943 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (943 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_943

theorem hpos_leaf_944 : order.symm (384 : Fin 1024) = (944 : Fin 1024) := by decide
#print axioms hpos_leaf_944

theorem w0_leaf_944 : w0 944 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_384 (F := M)
  rw [hpos_leaf_944] at hs
  calc w0 944 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (944 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (944 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_944

theorem w2_leaf_944 : w2 944 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_384 (F := M)
  rw [hpos_leaf_944] at hs
  calc w2 944 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (944 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (944 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_944

theorem hpos_leaf_945 : order.symm (385 : Fin 1024) = (945 : Fin 1024) := by decide
#print axioms hpos_leaf_945

theorem w0_leaf_945 : w0 945 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_385 (F := M)
  rw [hpos_leaf_945] at hs
  calc w0 945 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (945 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (945 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_945

theorem w2_leaf_945 : w2 945 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_385 (F := M)
  rw [hpos_leaf_945] at hs
  calc w2 945 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (945 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (945 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_945

theorem hpos_leaf_946 : order.symm (400 : Fin 1024) = (946 : Fin 1024) := by decide
#print axioms hpos_leaf_946

theorem w0_leaf_946 : w0 946 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_400 (F := M)
  rw [hpos_leaf_946] at hs
  calc w0 946 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (946 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (946 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_946

theorem w2_leaf_946 : w2 946 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_400 (F := M)
  rw [hpos_leaf_946] at hs
  calc w2 946 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (946 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (946 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_946

theorem hpos_leaf_947 : order.symm (401 : Fin 1024) = (947 : Fin 1024) := by decide
#print axioms hpos_leaf_947

theorem w0_leaf_947 : w0 947 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p0_transport_zero_original_401 (F := M)
  rw [hpos_leaf_947] at hs
  calc w0 947 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (947 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (947 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_947

theorem w2_leaf_947 : w2 947 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk13.p2_transport_zero_original_401 (F := M)
  rw [hpos_leaf_947] at hs
  calc w2 947 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (947 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (947 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_947

theorem hpos_leaf_948 : order.symm (416 : Fin 1024) = (948 : Fin 1024) := by decide
#print axioms hpos_leaf_948

theorem w0_leaf_948 : w0 948 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_416 (F := M)
  rw [hpos_leaf_948] at hs
  calc w0 948 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (948 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (948 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_948

theorem w2_leaf_948 : w2 948 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_416 (F := M)
  rw [hpos_leaf_948] at hs
  calc w2 948 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (948 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (948 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_948

theorem hpos_leaf_949 : order.symm (417 : Fin 1024) = (949 : Fin 1024) := by decide
#print axioms hpos_leaf_949

theorem w0_leaf_949 : w0 949 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_417 (F := M)
  rw [hpos_leaf_949] at hs
  calc w0 949 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (949 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (949 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_949

theorem w2_leaf_949 : w2 949 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_417 (F := M)
  rw [hpos_leaf_949] at hs
  calc w2 949 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (949 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (949 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_949

theorem hpos_leaf_950 : order.symm (432 : Fin 1024) = (950 : Fin 1024) := by decide
#print axioms hpos_leaf_950

theorem w0_leaf_950 : w0 950 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_432 (F := M)
  rw [hpos_leaf_950] at hs
  calc w0 950 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (950 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (950 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_950

theorem w2_leaf_950 : w2 950 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_432 (F := M)
  rw [hpos_leaf_950] at hs
  calc w2 950 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (950 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (950 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_950

theorem hpos_leaf_951 : order.symm (433 : Fin 1024) = (951 : Fin 1024) := by decide
#print axioms hpos_leaf_951

theorem w0_leaf_951 : w0 951 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_433 (F := M)
  rw [hpos_leaf_951] at hs
  calc w0 951 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (951 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (951 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_951

theorem w2_leaf_951 : w2 951 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_433 (F := M)
  rw [hpos_leaf_951] at hs
  calc w2 951 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (951 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (951 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_951

end
end AspisV8R19.R780Point02WeightSharedChunk13
