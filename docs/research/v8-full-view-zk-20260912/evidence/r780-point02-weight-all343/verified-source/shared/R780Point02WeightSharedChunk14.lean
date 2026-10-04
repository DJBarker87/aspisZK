import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk14
import AspisV8R19.R772Point02DualLeavesChunk15
import AspisV8R19.R772Point02DualLeavesChunk24
import AspisV8R19.R772Point02DualLeavesChunk25

namespace AspisV8R19.R780Point02WeightSharedChunk14
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_952 : order.symm (448 : Fin 1024) = (952 : Fin 1024) := by decide
#print axioms hpos_leaf_952

theorem w0_leaf_952 : w0 952 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p0_transport_zero_original_448 (F := M)
  rw [hpos_leaf_952] at hs
  calc w0 952 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (952 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (952 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_952

theorem w2_leaf_952 : w2 952 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk24.p2_transport_zero_original_448 (F := M)
  rw [hpos_leaf_952] at hs
  calc w2 952 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (952 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (952 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_952

theorem hpos_leaf_953 : order.symm (449 : Fin 1024) = (953 : Fin 1024) := by decide
#print axioms hpos_leaf_953

theorem w0_leaf_953 : w0 953 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_449 (F := M)
  rw [hpos_leaf_953] at hs
  calc w0 953 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (953 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (953 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_953

theorem w2_leaf_953 : w2 953 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_449 (F := M)
  rw [hpos_leaf_953] at hs
  calc w2 953 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (953 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (953 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_953

theorem hpos_leaf_954 : order.symm (464 : Fin 1024) = (954 : Fin 1024) := by decide
#print axioms hpos_leaf_954

theorem w0_leaf_954 : w0 954 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_464 (F := M)
  rw [hpos_leaf_954] at hs
  calc w0 954 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (954 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (954 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_954

theorem w2_leaf_954 : w2 954 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_464 (F := M)
  rw [hpos_leaf_954] at hs
  calc w2 954 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (954 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (954 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_954

theorem hpos_leaf_955 : order.symm (465 : Fin 1024) = (955 : Fin 1024) := by decide
#print axioms hpos_leaf_955

theorem w0_leaf_955 : w0 955 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_465 (F := M)
  rw [hpos_leaf_955] at hs
  calc w0 955 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (955 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (955 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_955

theorem w2_leaf_955 : w2 955 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_465 (F := M)
  rw [hpos_leaf_955] at hs
  calc w2 955 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (955 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (955 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_955

theorem hpos_leaf_956 : order.symm (480 : Fin 1024) = (956 : Fin 1024) := by decide
#print axioms hpos_leaf_956

theorem w0_leaf_956 : w0 956 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_480 (F := M)
  rw [hpos_leaf_956] at hs
  calc w0 956 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (956 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (956 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_956

theorem w2_leaf_956 : w2 956 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_480 (F := M)
  rw [hpos_leaf_956] at hs
  calc w2 956 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (956 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (956 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_956

theorem hpos_leaf_957 : order.symm (481 : Fin 1024) = (957 : Fin 1024) := by decide
#print axioms hpos_leaf_957

theorem w0_leaf_957 : w0 957 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_481 (F := M)
  rw [hpos_leaf_957] at hs
  calc w0 957 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (957 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (957 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_957

theorem w2_leaf_957 : w2 957 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_481 (F := M)
  rw [hpos_leaf_957] at hs
  calc w2 957 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (957 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (957 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_957

theorem hpos_leaf_958 : order.symm (496 : Fin 1024) = (958 : Fin 1024) := by decide
#print axioms hpos_leaf_958

theorem w0_leaf_958 : w0 958 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_496 (F := M)
  rw [hpos_leaf_958] at hs
  calc w0 958 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (958 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (958 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_958

theorem w2_leaf_958 : w2 958 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_496 (F := M)
  rw [hpos_leaf_958] at hs
  calc w2 958 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (958 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (958 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_958

theorem hpos_leaf_959 : order.symm (497 : Fin 1024) = (959 : Fin 1024) := by decide
#print axioms hpos_leaf_959

theorem w0_leaf_959 : w0 959 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_497 (F := M)
  rw [hpos_leaf_959] at hs
  calc w0 959 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (959 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (959 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_959

theorem w2_leaf_959 : w2 959 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_497 (F := M)
  rw [hpos_leaf_959] at hs
  calc w2 959 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (959 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (959 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_959

theorem hpos_leaf_960 : order.symm (512 : Fin 1024) = (960 : Fin 1024) := by decide
#print axioms hpos_leaf_960

theorem w0_leaf_960 : w0 960 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_512 (F := M)
  rw [hpos_leaf_960] at hs
  calc w0 960 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (960 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (960 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_960

theorem w2_leaf_960 : w2 960 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_512 (F := M)
  rw [hpos_leaf_960] at hs
  calc w2 960 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (960 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (960 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_960

theorem hpos_leaf_961 : order.symm (513 : Fin 1024) = (961 : Fin 1024) := by decide
#print axioms hpos_leaf_961

theorem w0_leaf_961 : w0 961 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_513 (F := M)
  rw [hpos_leaf_961] at hs
  calc w0 961 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (961 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (961 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_961

theorem w2_leaf_961 : w2 961 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_513 (F := M)
  rw [hpos_leaf_961] at hs
  calc w2 961 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (961 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (961 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_961

theorem hpos_leaf_962 : order.symm (528 : Fin 1024) = (962 : Fin 1024) := by decide
#print axioms hpos_leaf_962

theorem w0_leaf_962 : w0 962 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_528 (F := M)
  rw [hpos_leaf_962] at hs
  calc w0 962 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (962 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (962 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_962

theorem w2_leaf_962 : w2 962 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_528 (F := M)
  rw [hpos_leaf_962] at hs
  calc w2 962 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (962 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (962 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_962

theorem hpos_leaf_963 : order.symm (529 : Fin 1024) = (963 : Fin 1024) := by decide
#print axioms hpos_leaf_963

theorem w0_leaf_963 : w0 963 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_529 (F := M)
  rw [hpos_leaf_963] at hs
  calc w0 963 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (963 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (963 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_963

theorem w2_leaf_963 : w2 963 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_529 (F := M)
  rw [hpos_leaf_963] at hs
  calc w2 963 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (963 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (963 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_963

theorem hpos_leaf_964 : order.symm (544 : Fin 1024) = (964 : Fin 1024) := by decide
#print axioms hpos_leaf_964

theorem w0_leaf_964 : w0 964 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_544 (F := M)
  rw [hpos_leaf_964] at hs
  calc w0 964 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (964 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (964 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_964

theorem w2_leaf_964 : w2 964 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_544 (F := M)
  rw [hpos_leaf_964] at hs
  calc w2 964 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (964 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (964 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_964

theorem hpos_leaf_965 : order.symm (545 : Fin 1024) = (965 : Fin 1024) := by decide
#print axioms hpos_leaf_965

theorem w0_leaf_965 : w0 965 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_545 (F := M)
  rw [hpos_leaf_965] at hs
  calc w0 965 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (965 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (965 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_965

theorem w2_leaf_965 : w2 965 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_545 (F := M)
  rw [hpos_leaf_965] at hs
  calc w2 965 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (965 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (965 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_965

theorem hpos_leaf_966 : order.symm (560 : Fin 1024) = (966 : Fin 1024) := by decide
#print axioms hpos_leaf_966

theorem w0_leaf_966 : w0 966 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_560 (F := M)
  rw [hpos_leaf_966] at hs
  calc w0 966 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (966 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (966 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_966

theorem w2_leaf_966 : w2 966 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_560 (F := M)
  rw [hpos_leaf_966] at hs
  calc w2 966 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (966 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (966 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_966

theorem hpos_leaf_967 : order.symm (561 : Fin 1024) = (967 : Fin 1024) := by decide
#print axioms hpos_leaf_967

theorem w0_leaf_967 : w0 967 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_561 (F := M)
  rw [hpos_leaf_967] at hs
  calc w0 967 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (967 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (967 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_967

theorem w2_leaf_967 : w2 967 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_561 (F := M)
  rw [hpos_leaf_967] at hs
  calc w2 967 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (967 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (967 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_967

theorem hpos_leaf_968 : order.symm (576 : Fin 1024) = (968 : Fin 1024) := by decide
#print axioms hpos_leaf_968

theorem w0_leaf_968 : w0 968 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_576 (F := M)
  rw [hpos_leaf_968] at hs
  calc w0 968 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (968 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (968 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_968

theorem w2_leaf_968 : w2 968 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_576 (F := M)
  rw [hpos_leaf_968] at hs
  calc w2 968 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (968 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (968 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_968

theorem hpos_leaf_969 : order.symm (577 : Fin 1024) = (969 : Fin 1024) := by decide
#print axioms hpos_leaf_969

theorem w0_leaf_969 : w0 969 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_577 (F := M)
  rw [hpos_leaf_969] at hs
  calc w0 969 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (969 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (969 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_969

theorem w2_leaf_969 : w2 969 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_577 (F := M)
  rw [hpos_leaf_969] at hs
  calc w2 969 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (969 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (969 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_969

theorem hpos_leaf_970 : order.symm (592 : Fin 1024) = (970 : Fin 1024) := by decide
#print axioms hpos_leaf_970

theorem w0_leaf_970 : w0 970 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_592 (F := M)
  rw [hpos_leaf_970] at hs
  calc w0 970 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (970 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (970 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_970

theorem w2_leaf_970 : w2 970 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_592 (F := M)
  rw [hpos_leaf_970] at hs
  calc w2 970 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (970 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (970 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_970

theorem hpos_leaf_971 : order.symm (593 : Fin 1024) = (971 : Fin 1024) := by decide
#print axioms hpos_leaf_971

theorem w0_leaf_971 : w0 971 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_593 (F := M)
  rw [hpos_leaf_971] at hs
  calc w0 971 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (971 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (971 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_971

theorem w2_leaf_971 : w2 971 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_593 (F := M)
  rw [hpos_leaf_971] at hs
  calc w2 971 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (971 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (971 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_971

theorem hpos_leaf_972 : order.symm (608 : Fin 1024) = (972 : Fin 1024) := by decide
#print axioms hpos_leaf_972

theorem w0_leaf_972 : w0 972 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_608 (F := M)
  rw [hpos_leaf_972] at hs
  calc w0 972 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (972 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (972 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_972

theorem w2_leaf_972 : w2 972 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_608 (F := M)
  rw [hpos_leaf_972] at hs
  calc w2 972 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (972 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (972 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_972

theorem hpos_leaf_973 : order.symm (609 : Fin 1024) = (973 : Fin 1024) := by decide
#print axioms hpos_leaf_973

theorem w0_leaf_973 : w0 973 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_609 (F := M)
  rw [hpos_leaf_973] at hs
  calc w0 973 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (973 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (973 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_973

theorem w2_leaf_973 : w2 973 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_609 (F := M)
  rw [hpos_leaf_973] at hs
  calc w2 973 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (973 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (973 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_973

theorem hpos_leaf_974 : order.symm (624 : Fin 1024) = (974 : Fin 1024) := by decide
#print axioms hpos_leaf_974

theorem w0_leaf_974 : w0 974 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_624 (F := M)
  rw [hpos_leaf_974] at hs
  calc w0 974 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (974 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (974 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_974

theorem w2_leaf_974 : w2 974 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_624 (F := M)
  rw [hpos_leaf_974] at hs
  calc w2 974 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (974 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (974 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_974

theorem hpos_leaf_975 : order.symm (625 : Fin 1024) = (975 : Fin 1024) := by decide
#print axioms hpos_leaf_975

theorem w0_leaf_975 : w0 975 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p0_transport_zero_original_625 (F := M)
  rw [hpos_leaf_975] at hs
  calc w0 975 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (975 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (975 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_975

theorem w2_leaf_975 : w2 975 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk14.p2_transport_zero_original_625 (F := M)
  rw [hpos_leaf_975] at hs
  calc w2 975 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (975 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (975 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_975

theorem hpos_leaf_976 : order.symm (640 : Fin 1024) = (976 : Fin 1024) := by decide
#print axioms hpos_leaf_976

theorem w0_leaf_976 : w0 976 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_640 (F := M)
  rw [hpos_leaf_976] at hs
  calc w0 976 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (976 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (976 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_976

theorem w2_leaf_976 : w2 976 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_640 (F := M)
  rw [hpos_leaf_976] at hs
  calc w2 976 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (976 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (976 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_976

theorem hpos_leaf_977 : order.symm (641 : Fin 1024) = (977 : Fin 1024) := by decide
#print axioms hpos_leaf_977

theorem w0_leaf_977 : w0 977 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_641 (F := M)
  rw [hpos_leaf_977] at hs
  calc w0 977 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (977 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (977 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_977

theorem w2_leaf_977 : w2 977 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_641 (F := M)
  rw [hpos_leaf_977] at hs
  calc w2 977 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (977 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (977 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_977

theorem hpos_leaf_978 : order.symm (656 : Fin 1024) = (978 : Fin 1024) := by decide
#print axioms hpos_leaf_978

theorem w0_leaf_978 : w0 978 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_656 (F := M)
  rw [hpos_leaf_978] at hs
  calc w0 978 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (978 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (978 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_978

theorem w2_leaf_978 : w2 978 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_656 (F := M)
  rw [hpos_leaf_978] at hs
  calc w2 978 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (978 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (978 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_978

theorem hpos_leaf_979 : order.symm (657 : Fin 1024) = (979 : Fin 1024) := by decide
#print axioms hpos_leaf_979

theorem w0_leaf_979 : w0 979 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_657 (F := M)
  rw [hpos_leaf_979] at hs
  calc w0 979 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (979 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (979 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_979

theorem w2_leaf_979 : w2 979 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_657 (F := M)
  rw [hpos_leaf_979] at hs
  calc w2 979 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (979 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (979 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_979

theorem hpos_leaf_980 : order.symm (672 : Fin 1024) = (980 : Fin 1024) := by decide
#print axioms hpos_leaf_980

theorem w0_leaf_980 : w0 980 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_672 (F := M)
  rw [hpos_leaf_980] at hs
  calc w0 980 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (980 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (980 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_980

theorem w2_leaf_980 : w2 980 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_672 (F := M)
  rw [hpos_leaf_980] at hs
  calc w2 980 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (980 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (980 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_980

theorem hpos_leaf_981 : order.symm (673 : Fin 1024) = (981 : Fin 1024) := by decide
#print axioms hpos_leaf_981

theorem w0_leaf_981 : w0 981 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_673 (F := M)
  rw [hpos_leaf_981] at hs
  calc w0 981 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (981 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (981 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_981

theorem w2_leaf_981 : w2 981 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_673 (F := M)
  rw [hpos_leaf_981] at hs
  calc w2 981 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (981 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (981 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_981

theorem hpos_leaf_982 : order.symm (688 : Fin 1024) = (982 : Fin 1024) := by decide
#print axioms hpos_leaf_982

theorem w0_leaf_982 : w0 982 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p0_transport_zero_original_688 (F := M)
  rw [hpos_leaf_982] at hs
  calc w0 982 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (982 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (982 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_982

theorem w2_leaf_982 : w2 982 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk25.p2_transport_zero_original_688 (F := M)
  rw [hpos_leaf_982] at hs
  calc w2 982 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (982 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (982 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_982

theorem hpos_leaf_983 : order.symm (689 : Fin 1024) = (983 : Fin 1024) := by decide
#print axioms hpos_leaf_983

theorem w0_leaf_983 : w0 983 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p0_transport_zero_original_689 (F := M)
  rw [hpos_leaf_983] at hs
  calc w0 983 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (983 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (983 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_983

theorem w2_leaf_983 : w2 983 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk15.p2_transport_zero_original_689 (F := M)
  rw [hpos_leaf_983] at hs
  calc w2 983 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (983 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (983 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_983

end
end AspisV8R19.R780Point02WeightSharedChunk14
