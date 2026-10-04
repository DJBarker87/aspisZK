import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk09
import AspisV8R19.R772Point02DualLeavesChunk10
import AspisV8R19.R772Point02DualLeavesChunk22
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk30

namespace AspisV8R19.R780Point02WeightSharedChunk09
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_367 : order.symm (891 : Fin 1024) = (367 : Fin 1024) := by decide
#print axioms hpos_leaf_367

theorem w0_leaf_367 : w0 367 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_891 (F := M)
  rw [hpos_leaf_367] at hs
  calc w0 367 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (367 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (367 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_367

theorem w2_leaf_367 : w2 367 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_891 (F := M)
  rw [hpos_leaf_367] at hs
  calc w2 367 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (367 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (367 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_367

theorem hpos_leaf_368 : order.symm (906 : Fin 1024) = (368 : Fin 1024) := by decide
#print axioms hpos_leaf_368

theorem w0_leaf_368 : w0 368 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_906 (F := M)
  rw [hpos_leaf_368] at hs
  calc w0 368 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (368 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (368 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_368

theorem w2_leaf_368 : w2 368 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_906 (F := M)
  rw [hpos_leaf_368] at hs
  calc w2 368 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (368 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (368 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_368

theorem hpos_leaf_369 : order.symm (907 : Fin 1024) = (369 : Fin 1024) := by decide
#print axioms hpos_leaf_369

theorem w0_leaf_369 : w0 369 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_907 (F := M)
  rw [hpos_leaf_369] at hs
  calc w0 369 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (369 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (369 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_369

theorem w2_leaf_369 : w2 369 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_907 (F := M)
  rw [hpos_leaf_369] at hs
  calc w2 369 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (369 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (369 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_369

theorem hpos_leaf_370 : order.symm (922 : Fin 1024) = (370 : Fin 1024) := by decide
#print axioms hpos_leaf_370

theorem w0_leaf_370 : w0 370 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_922 (F := M)
  rw [hpos_leaf_370] at hs
  calc w0 370 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (370 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (370 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_370

theorem w2_leaf_370 : w2 370 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_922 (F := M)
  rw [hpos_leaf_370] at hs
  calc w2 370 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (370 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (370 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_370

theorem hpos_leaf_371 : order.symm (923 : Fin 1024) = (371 : Fin 1024) := by decide
#print axioms hpos_leaf_371

theorem w0_leaf_371 : w0 371 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_923 (F := M)
  rw [hpos_leaf_371] at hs
  calc w0 371 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (371 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (371 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_371

theorem w2_leaf_371 : w2 371 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_923 (F := M)
  rw [hpos_leaf_371] at hs
  calc w2 371 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (371 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (371 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_371

theorem hpos_leaf_372 : order.symm (938 : Fin 1024) = (372 : Fin 1024) := by decide
#print axioms hpos_leaf_372

theorem w0_leaf_372 : w0 372 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_938 (F := M)
  rw [hpos_leaf_372] at hs
  calc w0 372 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (372 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (372 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_372

theorem w2_leaf_372 : w2 372 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_938 (F := M)
  rw [hpos_leaf_372] at hs
  calc w2 372 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (372 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (372 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_372

theorem hpos_leaf_373 : order.symm (939 : Fin 1024) = (373 : Fin 1024) := by decide
#print axioms hpos_leaf_373

theorem w0_leaf_373 : w0 373 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_939 (F := M)
  rw [hpos_leaf_373] at hs
  calc w0 373 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (373 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (373 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_373

theorem w2_leaf_373 : w2 373 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_939 (F := M)
  rw [hpos_leaf_373] at hs
  calc w2 373 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (373 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (373 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_373

theorem hpos_leaf_374 : order.symm (954 : Fin 1024) = (374 : Fin 1024) := by decide
#print axioms hpos_leaf_374

theorem w0_leaf_374 : w0 374 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_954 (F := M)
  rw [hpos_leaf_374] at hs
  calc w0 374 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (374 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (374 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_374

theorem w2_leaf_374 : w2 374 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_954 (F := M)
  rw [hpos_leaf_374] at hs
  calc w2 374 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (374 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (374 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_374

theorem hpos_leaf_375 : order.symm (955 : Fin 1024) = (375 : Fin 1024) := by decide
#print axioms hpos_leaf_375

theorem w0_leaf_375 : w0 375 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_955 (F := M)
  rw [hpos_leaf_375] at hs
  calc w0 375 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (375 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (375 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_375

theorem w2_leaf_375 : w2 375 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_955 (F := M)
  rw [hpos_leaf_375] at hs
  calc w2 375 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (375 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (375 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_375

theorem hpos_leaf_376 : order.symm (970 : Fin 1024) = (376 : Fin 1024) := by decide
#print axioms hpos_leaf_376

theorem w0_leaf_376 : w0 376 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_970 (F := M)
  rw [hpos_leaf_376] at hs
  calc w0 376 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (376 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (376 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_376

theorem w2_leaf_376 : w2 376 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_970 (F := M)
  rw [hpos_leaf_376] at hs
  calc w2 376 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (376 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (376 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_376

theorem hpos_leaf_377 : order.symm (971 : Fin 1024) = (377 : Fin 1024) := by decide
#print axioms hpos_leaf_377

theorem w0_leaf_377 : w0 377 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_971 (F := M)
  rw [hpos_leaf_377] at hs
  calc w0 377 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (377 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (377 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_377

theorem w2_leaf_377 : w2 377 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_971 (F := M)
  rw [hpos_leaf_377] at hs
  calc w2 377 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (377 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (377 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_377

theorem hpos_leaf_378 : order.symm (986 : Fin 1024) = (378 : Fin 1024) := by decide
#print axioms hpos_leaf_378

theorem w0_leaf_378 : w0 378 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_986 (F := M)
  rw [hpos_leaf_378] at hs
  calc w0 378 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (378 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (378 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_378

theorem w2_leaf_378 : w2 378 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_986 (F := M)
  rw [hpos_leaf_378] at hs
  calc w2 378 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (378 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (378 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_378

theorem hpos_leaf_379 : order.symm (987 : Fin 1024) = (379 : Fin 1024) := by decide
#print axioms hpos_leaf_379

theorem w0_leaf_379 : w0 379 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_987 (F := M)
  rw [hpos_leaf_379] at hs
  calc w0 379 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (379 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (379 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_379

theorem w2_leaf_379 : w2 379 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_987 (F := M)
  rw [hpos_leaf_379] at hs
  calc w2 379 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (379 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (379 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_379

theorem hpos_leaf_380 : order.symm (1002 : Fin 1024) = (380 : Fin 1024) := by decide
#print axioms hpos_leaf_380

theorem w0_leaf_380 : w0 380 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1002 (F := M)
  rw [hpos_leaf_380] at hs
  calc w0 380 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (380 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (380 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_380

theorem w2_leaf_380 : w2 380 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1002 (F := M)
  rw [hpos_leaf_380] at hs
  calc w2 380 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (380 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (380 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_380

theorem hpos_leaf_381 : order.symm (1003 : Fin 1024) = (381 : Fin 1024) := by decide
#print axioms hpos_leaf_381

theorem w0_leaf_381 : w0 381 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_1003 (F := M)
  rw [hpos_leaf_381] at hs
  calc w0 381 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (381 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (381 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_381

theorem w2_leaf_381 : w2 381 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_1003 (F := M)
  rw [hpos_leaf_381] at hs
  calc w2 381 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (381 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (381 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_381

theorem hpos_leaf_382 : order.symm (1018 : Fin 1024) = (382 : Fin 1024) := by decide
#print axioms hpos_leaf_382

theorem w0_leaf_382 : w0 382 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p0_transport_zero_original_1018 (F := M)
  rw [hpos_leaf_382] at hs
  calc w0 382 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (382 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (382 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_382

theorem w2_leaf_382 : w2 382 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk22.p2_transport_zero_original_1018 (F := M)
  rw [hpos_leaf_382] at hs
  calc w2 382 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (382 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (382 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_382

theorem hpos_leaf_383 : order.symm (1019 : Fin 1024) = (383 : Fin 1024) := by decide
#print axioms hpos_leaf_383

theorem w0_leaf_383 : w0 383 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_1019 (F := M)
  rw [hpos_leaf_383] at hs
  calc w0 383 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (383 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (383 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_383

theorem w2_leaf_383 : w2 383 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_1019 (F := M)
  rw [hpos_leaf_383] at hs
  calc w2 383 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (383 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (383 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_383

theorem hpos_leaf_384 : order.symm (8 : Fin 1024) = (384 : Fin 1024) := by decide
#print axioms hpos_leaf_384

theorem w0_leaf_384 : w0 384 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p0_transport_zero_original_8 (F := M)
  rw [hpos_leaf_384] at hs
  calc w0 384 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (384 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (384 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_384

theorem w2_leaf_384 : w2 384 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk09.p2_transport_zero_original_8 (F := M)
  rw [hpos_leaf_384] at hs
  calc w2 384 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (384 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (384 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_384

theorem hpos_leaf_385 : order.symm (9 : Fin 1024) = (385 : Fin 1024) := by decide
#print axioms hpos_leaf_385

theorem w0_leaf_385 : w0 385 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_9 (F := M)
  rw [hpos_leaf_385] at hs
  calc w0 385 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (385 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (385 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_385

theorem w2_leaf_385 : w2 385 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_9 (F := M)
  rw [hpos_leaf_385] at hs
  calc w2 385 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (385 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (385 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_385

theorem hpos_leaf_386 : order.symm (24 : Fin 1024) = (386 : Fin 1024) := by decide
#print axioms hpos_leaf_386

theorem w0_leaf_386 : w0 386 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_24 (F := M)
  rw [hpos_leaf_386] at hs
  calc w0 386 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (386 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (386 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_386

theorem w2_leaf_386 : w2 386 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_24 (F := M)
  rw [hpos_leaf_386] at hs
  calc w2 386 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (386 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (386 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_386

theorem hpos_leaf_448 : order.symm (520 : Fin 1024) = (448 : Fin 1024) := by decide
#print axioms hpos_leaf_448

theorem w0_leaf_448 : w0 448 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_520 (F := M)
  rw [hpos_leaf_448] at hs
  calc w0 448 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (448 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (448 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_448

theorem w2_leaf_448 : w2 448 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_520 (F := M)
  rw [hpos_leaf_448] at hs
  calc w2 448 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (448 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (448 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_448

theorem hpos_leaf_449 : order.symm (521 : Fin 1024) = (449 : Fin 1024) := by decide
#print axioms hpos_leaf_449

theorem w0_leaf_449 : w0 449 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_521 (F := M)
  rw [hpos_leaf_449] at hs
  calc w0 449 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (449 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (449 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_449

theorem w2_leaf_449 : w2 449 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_521 (F := M)
  rw [hpos_leaf_449] at hs
  calc w2 449 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (449 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (449 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_449

theorem hpos_leaf_450 : order.symm (536 : Fin 1024) = (450 : Fin 1024) := by decide
#print axioms hpos_leaf_450

theorem w0_leaf_450 : w0 450 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p0_transport_zero_original_536 (F := M)
  rw [hpos_leaf_450] at hs
  calc w0 450 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (450 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (450 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_450

theorem w2_leaf_450 : w2 450 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk10.p2_transport_zero_original_536 (F := M)
  rw [hpos_leaf_450] at hs
  calc w2 450 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (450 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (450 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_450

theorem hpos_leaf_480 : order.symm (776 : Fin 1024) = (480 : Fin 1024) := by decide
#print axioms hpos_leaf_480

theorem w0_leaf_480 : w0 480 = ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_776 (F := M)
  rw [hpos_leaf_480] at hs
  calc w0 480 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (480 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (480 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_480

theorem w2_leaf_480 : w2 480 = ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_776 (F := M)
  rw [hpos_leaf_480] at hs
  calc w2 480 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (480 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (480 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_480

theorem hpos_leaf_481 : order.symm (777 : Fin 1024) = (481 : Fin 1024) := by decide
#print axioms hpos_leaf_481

theorem w0_leaf_481 : w0 481 = ([1, 1, -1, -2, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_777 (F := M)
  rw [hpos_leaf_481] at hs
  calc w0 481 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (481 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (481 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_481

theorem w2_leaf_481 : w2 481 = ([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_777 (F := M)
  rw [hpos_leaf_481] at hs
  calc w2 481 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (481 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (481 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_481

theorem hpos_leaf_482 : order.symm (792 : Fin 1024) = (482 : Fin 1024) := by decide
#print axioms hpos_leaf_482

theorem w0_leaf_482 : w0 482 = ([1, 1, -1, -2, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_792 (F := M)
  rw [hpos_leaf_482] at hs
  calc w0 482 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (482 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (482 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_482

theorem w2_leaf_482 : w2 482 = ([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_792 (F := M)
  rw [hpos_leaf_482] at hs
  calc w2 482 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (482 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (482 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_482

theorem hpos_leaf_496 : order.symm (904 : Fin 1024) = (496 : Fin 1024) := by decide
#print axioms hpos_leaf_496

theorem w0_leaf_496 : w0 496 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_904 (F := M)
  rw [hpos_leaf_496] at hs
  calc w0 496 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (496 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (496 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_496

theorem w2_leaf_496 : w2 496 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_904 (F := M)
  rw [hpos_leaf_496] at hs
  calc w2 496 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (496 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (496 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_496

theorem hpos_leaf_497 : order.symm (905 : Fin 1024) = (497 : Fin 1024) := by decide
#print axioms hpos_leaf_497

theorem w0_leaf_497 : w0 497 = ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_905 (F := M)
  rw [hpos_leaf_497] at hs
  calc w0 497 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (497 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (497 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_497

theorem w2_leaf_497 : w2 497 = ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_905 (F := M)
  rw [hpos_leaf_497] at hs
  calc w2 497 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (497 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (497 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_497

theorem hpos_leaf_498 : order.symm (920 : Fin 1024) = (498 : Fin 1024) := by decide
#print axioms hpos_leaf_498

theorem w0_leaf_498 : w0 498 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_920 (F := M)
  rw [hpos_leaf_498] at hs
  calc w0 498 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (498 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (498 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_498

theorem w2_leaf_498 : w2 498 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_920 (F := M)
  rw [hpos_leaf_498] at hs
  calc w2 498 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (498 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (498 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_498

theorem hpos_leaf_499 : order.symm (921 : Fin 1024) = (499 : Fin 1024) := by decide
#print axioms hpos_leaf_499

theorem w0_leaf_499 : w0 499 = ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_921 (F := M)
  rw [hpos_leaf_499] at hs
  calc w0 499 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (499 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (499 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_499

theorem w2_leaf_499 : w2 499 = ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_921 (F := M)
  rw [hpos_leaf_499] at hs
  calc w2 499 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (499 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (499 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_499

theorem hpos_leaf_500 : order.symm (936 : Fin 1024) = (500 : Fin 1024) := by decide
#print axioms hpos_leaf_500

theorem w0_leaf_500 : w0 500 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p0_transport_exact_original_936 (F := M)
  rw [hpos_leaf_500] at hs
  calc w0 500 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (500 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (500 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, -2, 1, -1] : List M).prod := hs

#print axioms w0_leaf_500

theorem w2_leaf_500 : w2 500 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk30.p2_transport_exact_original_936 (F := M)
  rw [hpos_leaf_500] at hs
  calc w2 500 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (500 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (500 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, 3, 1, -1] : List M).prod := hs

#print axioms w2_leaf_500

theorem hpos_leaf_501 : order.symm (937 : Fin 1024) = (501 : Fin 1024) := by decide
#print axioms hpos_leaf_501

theorem w0_leaf_501 : w0 501 = ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_937 (F := M)
  rw [hpos_leaf_501] at hs
  calc w0 501 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (501 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (501 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, -2, 1, 2] : List M).prod := hs

#print axioms w0_leaf_501

theorem w2_leaf_501 : w2 501 = ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_937 (F := M)
  rw [hpos_leaf_501] at hs
  calc w2 501 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (501 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (501 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, 3, 1, 2] : List M).prod := hs

#print axioms w2_leaf_501

end
end AspisV8R19.R780Point02WeightSharedChunk09
