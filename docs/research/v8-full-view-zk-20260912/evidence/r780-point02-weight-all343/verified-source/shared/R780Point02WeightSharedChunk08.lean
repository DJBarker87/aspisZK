import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk08
import AspisV8R19.R772Point02DualLeavesChunk09
import AspisV8R19.R772Point02DualLeavesChunk21

namespace AspisV8R19.R780Point02WeightSharedChunk08
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_335 : order.symm (635 : Fin 1024) = (335 : Fin 1024) := by decide
#print axioms hpos_leaf_335

theorem w0_leaf_335 : w0 335 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_635 (F := M)
  rw [hpos_leaf_335] at hs
  calc w0 335 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (335 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (335 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_335

theorem w2_leaf_335 : w2 335 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_635 (F := M)
  rw [hpos_leaf_335] at hs
  calc w2 335 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (335 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (335 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_335

theorem hpos_leaf_336 : order.symm (650 : Fin 1024) = (336 : Fin 1024) := by decide
#print axioms hpos_leaf_336

theorem w0_leaf_336 : w0 336 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_650 (F := M)
  rw [hpos_leaf_336] at hs
  calc w0 336 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (336 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (336 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_336

theorem w2_leaf_336 : w2 336 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_650 (F := M)
  rw [hpos_leaf_336] at hs
  calc w2 336 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (336 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (336 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_336

theorem hpos_leaf_337 : order.symm (651 : Fin 1024) = (337 : Fin 1024) := by decide
#print axioms hpos_leaf_337

theorem w0_leaf_337 : w0 337 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_651 (F := M)
  rw [hpos_leaf_337] at hs
  calc w0 337 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (337 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (337 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_337

theorem w2_leaf_337 : w2 337 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_651 (F := M)
  rw [hpos_leaf_337] at hs
  calc w2 337 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (337 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (337 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_337

theorem hpos_leaf_338 : order.symm (666 : Fin 1024) = (338 : Fin 1024) := by decide
#print axioms hpos_leaf_338

theorem w0_leaf_338 : w0 338 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_666 (F := M)
  rw [hpos_leaf_338] at hs
  calc w0 338 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (338 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (338 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_338

theorem w2_leaf_338 : w2 338 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_666 (F := M)
  rw [hpos_leaf_338] at hs
  calc w2 338 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (338 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (338 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_338

theorem hpos_leaf_339 : order.symm (667 : Fin 1024) = (339 : Fin 1024) := by decide
#print axioms hpos_leaf_339

theorem w0_leaf_339 : w0 339 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_667 (F := M)
  rw [hpos_leaf_339] at hs
  calc w0 339 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (339 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (339 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_339

theorem w2_leaf_339 : w2 339 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_667 (F := M)
  rw [hpos_leaf_339] at hs
  calc w2 339 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (339 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (339 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_339

theorem hpos_leaf_340 : order.symm (682 : Fin 1024) = (340 : Fin 1024) := by decide
#print axioms hpos_leaf_340

theorem w0_leaf_340 : w0 340 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_682 (F := M)
  rw [hpos_leaf_340] at hs
  calc w0 340 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (340 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (340 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_340

theorem w2_leaf_340 : w2 340 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_682 (F := M)
  rw [hpos_leaf_340] at hs
  calc w2 340 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (340 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (340 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_340

theorem hpos_leaf_341 : order.symm (683 : Fin 1024) = (341 : Fin 1024) := by decide
#print axioms hpos_leaf_341

theorem w0_leaf_341 : w0 341 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_683 (F := M)
  rw [hpos_leaf_341] at hs
  calc w0 341 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (341 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (341 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_341

theorem w2_leaf_341 : w2 341 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_683 (F := M)
  rw [hpos_leaf_341] at hs
  calc w2 341 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (341 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (341 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_341

theorem hpos_leaf_342 : order.symm (698 : Fin 1024) = (342 : Fin 1024) := by decide
#print axioms hpos_leaf_342

theorem w0_leaf_342 : w0 342 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_698 (F := M)
  rw [hpos_leaf_342] at hs
  calc w0 342 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (342 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (342 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_342

theorem w2_leaf_342 : w2 342 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_698 (F := M)
  rw [hpos_leaf_342] at hs
  calc w2 342 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (342 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (342 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_342

theorem hpos_leaf_343 : order.symm (699 : Fin 1024) = (343 : Fin 1024) := by decide
#print axioms hpos_leaf_343

theorem w0_leaf_343 : w0 343 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_699 (F := M)
  rw [hpos_leaf_343] at hs
  calc w0 343 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (343 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (343 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_343

theorem w2_leaf_343 : w2 343 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_699 (F := M)
  rw [hpos_leaf_343] at hs
  calc w2 343 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (343 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (343 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_343

theorem hpos_leaf_344 : order.symm (714 : Fin 1024) = (344 : Fin 1024) := by decide
#print axioms hpos_leaf_344

theorem w0_leaf_344 : w0 344 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_714 (F := M)
  rw [hpos_leaf_344] at hs
  calc w0 344 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (344 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (344 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_344

theorem w2_leaf_344 : w2 344 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_714 (F := M)
  rw [hpos_leaf_344] at hs
  calc w2 344 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (344 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (344 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_344

theorem hpos_leaf_345 : order.symm (715 : Fin 1024) = (345 : Fin 1024) := by decide
#print axioms hpos_leaf_345

theorem w0_leaf_345 : w0 345 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_715 (F := M)
  rw [hpos_leaf_345] at hs
  calc w0 345 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (345 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (345 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_345

theorem w2_leaf_345 : w2 345 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_715 (F := M)
  rw [hpos_leaf_345] at hs
  calc w2 345 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (345 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (345 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_345

theorem hpos_leaf_346 : order.symm (730 : Fin 1024) = (346 : Fin 1024) := by decide
#print axioms hpos_leaf_346

theorem w0_leaf_346 : w0 346 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_730 (F := M)
  rw [hpos_leaf_346] at hs
  calc w0 346 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (346 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (346 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_346

theorem w2_leaf_346 : w2 346 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_730 (F := M)
  rw [hpos_leaf_346] at hs
  calc w2 346 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (346 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (346 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_346

theorem hpos_leaf_347 : order.symm (731 : Fin 1024) = (347 : Fin 1024) := by decide
#print axioms hpos_leaf_347

theorem w0_leaf_347 : w0 347 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_731 (F := M)
  rw [hpos_leaf_347] at hs
  calc w0 347 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (347 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (347 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_347

theorem w2_leaf_347 : w2 347 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_731 (F := M)
  rw [hpos_leaf_347] at hs
  calc w2 347 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (347 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (347 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_347

theorem hpos_leaf_348 : order.symm (746 : Fin 1024) = (348 : Fin 1024) := by decide
#print axioms hpos_leaf_348

theorem w0_leaf_348 : w0 348 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_746 (F := M)
  rw [hpos_leaf_348] at hs
  calc w0 348 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (348 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (348 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_348

theorem w2_leaf_348 : w2 348 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_746 (F := M)
  rw [hpos_leaf_348] at hs
  calc w2 348 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (348 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (348 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_348

theorem hpos_leaf_349 : order.symm (747 : Fin 1024) = (349 : Fin 1024) := by decide
#print axioms hpos_leaf_349

theorem w0_leaf_349 : w0 349 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_747 (F := M)
  rw [hpos_leaf_349] at hs
  calc w0 349 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (349 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (349 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_349

theorem w2_leaf_349 : w2 349 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_747 (F := M)
  rw [hpos_leaf_349] at hs
  calc w2 349 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (349 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (349 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_349

theorem hpos_leaf_350 : order.symm (762 : Fin 1024) = (350 : Fin 1024) := by decide
#print axioms hpos_leaf_350

theorem w0_leaf_350 : w0 350 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_762 (F := M)
  rw [hpos_leaf_350] at hs
  calc w0 350 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (350 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (350 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_350

theorem w2_leaf_350 : w2 350 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_762 (F := M)
  rw [hpos_leaf_350] at hs
  calc w2 350 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (350 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (350 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_350

theorem hpos_leaf_351 : order.symm (763 : Fin 1024) = (351 : Fin 1024) := by decide
#print axioms hpos_leaf_351

theorem w0_leaf_351 : w0 351 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_763 (F := M)
  rw [hpos_leaf_351] at hs
  calc w0 351 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (351 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (351 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_351

theorem w2_leaf_351 : w2 351 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_763 (F := M)
  rw [hpos_leaf_351] at hs
  calc w2 351 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (351 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (351 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_351

theorem hpos_leaf_352 : order.symm (778 : Fin 1024) = (352 : Fin 1024) := by decide
#print axioms hpos_leaf_352

theorem w0_leaf_352 : w0 352 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_778 (F := M)
  rw [hpos_leaf_352] at hs
  calc w0 352 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (352 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (352 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_352

theorem w2_leaf_352 : w2 352 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_778 (F := M)
  rw [hpos_leaf_352] at hs
  calc w2 352 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (352 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (352 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_352

theorem hpos_leaf_353 : order.symm (779 : Fin 1024) = (353 : Fin 1024) := by decide
#print axioms hpos_leaf_353

theorem w0_leaf_353 : w0 353 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_779 (F := M)
  rw [hpos_leaf_353] at hs
  calc w0 353 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (353 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (353 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_353

theorem w2_leaf_353 : w2 353 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_779 (F := M)
  rw [hpos_leaf_353] at hs
  calc w2 353 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (353 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (353 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_353

theorem hpos_leaf_354 : order.symm (794 : Fin 1024) = (354 : Fin 1024) := by decide
#print axioms hpos_leaf_354

theorem w0_leaf_354 : w0 354 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_794 (F := M)
  rw [hpos_leaf_354] at hs
  calc w0 354 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (354 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (354 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_354

theorem w2_leaf_354 : w2 354 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_794 (F := M)
  rw [hpos_leaf_354] at hs
  calc w2 354 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (354 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (354 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_354

theorem hpos_leaf_355 : order.symm (795 : Fin 1024) = (355 : Fin 1024) := by decide
#print axioms hpos_leaf_355

theorem w0_leaf_355 : w0 355 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_795 (F := M)
  rw [hpos_leaf_355] at hs
  calc w0 355 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (355 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (355 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_355

theorem w2_leaf_355 : w2 355 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_795 (F := M)
  rw [hpos_leaf_355] at hs
  calc w2 355 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (355 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (355 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_355

theorem hpos_leaf_356 : order.symm (810 : Fin 1024) = (356 : Fin 1024) := by decide
#print axioms hpos_leaf_356

theorem w0_leaf_356 : w0 356 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_810 (F := M)
  rw [hpos_leaf_356] at hs
  calc w0 356 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (356 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (356 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_356

theorem w2_leaf_356 : w2 356 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_810 (F := M)
  rw [hpos_leaf_356] at hs
  calc w2 356 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (356 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (356 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_356

theorem hpos_leaf_357 : order.symm (811 : Fin 1024) = (357 : Fin 1024) := by decide
#print axioms hpos_leaf_357

theorem w0_leaf_357 : w0 357 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_811 (F := M)
  rw [hpos_leaf_357] at hs
  calc w0 357 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (357 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (357 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_357

theorem w2_leaf_357 : w2 357 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_811 (F := M)
  rw [hpos_leaf_357] at hs
  calc w2 357 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (357 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (357 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_357

theorem hpos_leaf_358 : order.symm (826 : Fin 1024) = (358 : Fin 1024) := by decide
#print axioms hpos_leaf_358

theorem w0_leaf_358 : w0 358 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_826 (F := M)
  rw [hpos_leaf_358] at hs
  calc w0 358 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (358 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (358 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_358

theorem w2_leaf_358 : w2 358 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_826 (F := M)
  rw [hpos_leaf_358] at hs
  calc w2 358 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (358 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (358 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_358

theorem hpos_leaf_359 : order.symm (827 : Fin 1024) = (359 : Fin 1024) := by decide
#print axioms hpos_leaf_359

theorem w0_leaf_359 : w0 359 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_827 (F := M)
  rw [hpos_leaf_359] at hs
  calc w0 359 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (359 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (359 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_359

theorem w2_leaf_359 : w2 359 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_827 (F := M)
  rw [hpos_leaf_359] at hs
  calc w2 359 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (359 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (359 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_359

theorem hpos_leaf_360 : order.symm (842 : Fin 1024) = (360 : Fin 1024) := by decide
#print axioms hpos_leaf_360

theorem w0_leaf_360 : w0 360 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_842 (F := M)
  rw [hpos_leaf_360] at hs
  calc w0 360 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (360 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (360 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_360

theorem w2_leaf_360 : w2 360 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_842 (F := M)
  rw [hpos_leaf_360] at hs
  calc w2 360 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (360 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (360 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_360

theorem hpos_leaf_361 : order.symm (843 : Fin 1024) = (361 : Fin 1024) := by decide
#print axioms hpos_leaf_361

theorem w0_leaf_361 : w0 361 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_843 (F := M)
  rw [hpos_leaf_361] at hs
  calc w0 361 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (361 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (361 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_361

theorem w2_leaf_361 : w2 361 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_843 (F := M)
  rw [hpos_leaf_361] at hs
  calc w2 361 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (361 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (361 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_361

theorem hpos_leaf_362 : order.symm (858 : Fin 1024) = (362 : Fin 1024) := by decide
#print axioms hpos_leaf_362

theorem w0_leaf_362 : w0 362 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_858 (F := M)
  rw [hpos_leaf_362] at hs
  calc w0 362 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (362 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (362 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_362

theorem w2_leaf_362 : w2 362 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_858 (F := M)
  rw [hpos_leaf_362] at hs
  calc w2 362 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (362 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (362 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_362

theorem hpos_leaf_363 : order.symm (859 : Fin 1024) = (363 : Fin 1024) := by decide
#print axioms hpos_leaf_363

theorem w0_leaf_363 : w0 363 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_859 (F := M)
  rw [hpos_leaf_363] at hs
  calc w0 363 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (363 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (363 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_363

theorem w2_leaf_363 : w2 363 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_859 (F := M)
  rw [hpos_leaf_363] at hs
  calc w2 363 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (363 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (363 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_363

theorem hpos_leaf_364 : order.symm (874 : Fin 1024) = (364 : Fin 1024) := by decide
#print axioms hpos_leaf_364

theorem w0_leaf_364 : w0 364 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_874 (F := M)
  rw [hpos_leaf_364] at hs
  calc w0 364 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (364 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (364 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_364

theorem w2_leaf_364 : w2 364 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_874 (F := M)
  rw [hpos_leaf_364] at hs
  calc w2 364 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (364 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (364 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_364

theorem hpos_leaf_365 : order.symm (875 : Fin 1024) = (365 : Fin 1024) := by decide
#print axioms hpos_leaf_365

theorem w0_leaf_365 : w0 365 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_875 (F := M)
  rw [hpos_leaf_365] at hs
  calc w0 365 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (365 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (365 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_365

theorem w2_leaf_365 : w2 365 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_875 (F := M)
  rw [hpos_leaf_365] at hs
  calc w2 365 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (365 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (365 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_365

theorem hpos_leaf_366 : order.symm (890 : Fin 1024) = (366 : Fin 1024) := by decide
#print axioms hpos_leaf_366

theorem w0_leaf_366 : w0 366 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_890 (F := M)
  rw [hpos_leaf_366] at hs
  calc w0 366 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (366 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (366 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_366

theorem w2_leaf_366 : w2 366 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_890 (F := M)
  rw [hpos_leaf_366] at hs
  calc w2 366 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (366 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (366 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_366

end
end AspisV8R19.R780Point02WeightSharedChunk08
