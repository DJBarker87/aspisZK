import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk07
import AspisV8R19.R772Point02DualLeavesChunk08
import AspisV8R19.R772Point02DualLeavesChunk20
import AspisV8R19.R772Point02DualLeavesChunk21

namespace AspisV8R19.R780Point02WeightSharedChunk07
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_303 : order.symm (379 : Fin 1024) = (303 : Fin 1024) := by decide
#print axioms hpos_leaf_303

theorem w0_leaf_303 : w0 303 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_379 (F := M)
  rw [hpos_leaf_303] at hs
  calc w0 303 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (303 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (303 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_303

theorem w2_leaf_303 : w2 303 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_379 (F := M)
  rw [hpos_leaf_303] at hs
  calc w2 303 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (303 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (303 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_303

theorem hpos_leaf_304 : order.symm (394 : Fin 1024) = (304 : Fin 1024) := by decide
#print axioms hpos_leaf_304

theorem w0_leaf_304 : w0 304 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_394 (F := M)
  rw [hpos_leaf_304] at hs
  calc w0 304 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (304 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (304 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_304

theorem w2_leaf_304 : w2 304 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_394 (F := M)
  rw [hpos_leaf_304] at hs
  calc w2 304 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (304 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (304 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_304

theorem hpos_leaf_305 : order.symm (395 : Fin 1024) = (305 : Fin 1024) := by decide
#print axioms hpos_leaf_305

theorem w0_leaf_305 : w0 305 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_395 (F := M)
  rw [hpos_leaf_305] at hs
  calc w0 305 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (305 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (305 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_305

theorem w2_leaf_305 : w2 305 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_395 (F := M)
  rw [hpos_leaf_305] at hs
  calc w2 305 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (305 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (305 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_305

theorem hpos_leaf_306 : order.symm (410 : Fin 1024) = (306 : Fin 1024) := by decide
#print axioms hpos_leaf_306

theorem w0_leaf_306 : w0 306 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_410 (F := M)
  rw [hpos_leaf_306] at hs
  calc w0 306 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (306 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (306 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_306

theorem w2_leaf_306 : w2 306 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_410 (F := M)
  rw [hpos_leaf_306] at hs
  calc w2 306 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (306 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (306 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_306

theorem hpos_leaf_307 : order.symm (411 : Fin 1024) = (307 : Fin 1024) := by decide
#print axioms hpos_leaf_307

theorem w0_leaf_307 : w0 307 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_411 (F := M)
  rw [hpos_leaf_307] at hs
  calc w0 307 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (307 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (307 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_307

theorem w2_leaf_307 : w2 307 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_411 (F := M)
  rw [hpos_leaf_307] at hs
  calc w2 307 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (307 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (307 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_307

theorem hpos_leaf_308 : order.symm (426 : Fin 1024) = (308 : Fin 1024) := by decide
#print axioms hpos_leaf_308

theorem w0_leaf_308 : w0 308 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_426 (F := M)
  rw [hpos_leaf_308] at hs
  calc w0 308 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (308 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (308 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_308

theorem w2_leaf_308 : w2 308 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_426 (F := M)
  rw [hpos_leaf_308] at hs
  calc w2 308 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (308 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (308 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_308

theorem hpos_leaf_309 : order.symm (427 : Fin 1024) = (309 : Fin 1024) := by decide
#print axioms hpos_leaf_309

theorem w0_leaf_309 : w0 309 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_427 (F := M)
  rw [hpos_leaf_309] at hs
  calc w0 309 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (309 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (309 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_309

theorem w2_leaf_309 : w2 309 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_427 (F := M)
  rw [hpos_leaf_309] at hs
  calc w2 309 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (309 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (309 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_309

theorem hpos_leaf_310 : order.symm (442 : Fin 1024) = (310 : Fin 1024) := by decide
#print axioms hpos_leaf_310

theorem w0_leaf_310 : w0 310 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_442 (F := M)
  rw [hpos_leaf_310] at hs
  calc w0 310 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (310 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (310 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_310

theorem w2_leaf_310 : w2 310 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_442 (F := M)
  rw [hpos_leaf_310] at hs
  calc w2 310 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (310 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (310 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_310

theorem hpos_leaf_311 : order.symm (443 : Fin 1024) = (311 : Fin 1024) := by decide
#print axioms hpos_leaf_311

theorem w0_leaf_311 : w0 311 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_443 (F := M)
  rw [hpos_leaf_311] at hs
  calc w0 311 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (311 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (311 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_311

theorem w2_leaf_311 : w2 311 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_443 (F := M)
  rw [hpos_leaf_311] at hs
  calc w2 311 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (311 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (311 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_311

theorem hpos_leaf_312 : order.symm (458 : Fin 1024) = (312 : Fin 1024) := by decide
#print axioms hpos_leaf_312

theorem w0_leaf_312 : w0 312 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_458 (F := M)
  rw [hpos_leaf_312] at hs
  calc w0 312 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (312 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (312 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_312

theorem w2_leaf_312 : w2 312 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_458 (F := M)
  rw [hpos_leaf_312] at hs
  calc w2 312 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (312 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (312 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_312

theorem hpos_leaf_313 : order.symm (459 : Fin 1024) = (313 : Fin 1024) := by decide
#print axioms hpos_leaf_313

theorem w0_leaf_313 : w0 313 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_459 (F := M)
  rw [hpos_leaf_313] at hs
  calc w0 313 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (313 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (313 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_313

theorem w2_leaf_313 : w2 313 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_459 (F := M)
  rw [hpos_leaf_313] at hs
  calc w2 313 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (313 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (313 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_313

theorem hpos_leaf_314 : order.symm (474 : Fin 1024) = (314 : Fin 1024) := by decide
#print axioms hpos_leaf_314

theorem w0_leaf_314 : w0 314 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_474 (F := M)
  rw [hpos_leaf_314] at hs
  calc w0 314 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (314 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (314 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_314

theorem w2_leaf_314 : w2 314 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_474 (F := M)
  rw [hpos_leaf_314] at hs
  calc w2 314 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (314 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (314 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_314

theorem hpos_leaf_315 : order.symm (475 : Fin 1024) = (315 : Fin 1024) := by decide
#print axioms hpos_leaf_315

theorem w0_leaf_315 : w0 315 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_475 (F := M)
  rw [hpos_leaf_315] at hs
  calc w0 315 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (315 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (315 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_315

theorem w2_leaf_315 : w2 315 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_475 (F := M)
  rw [hpos_leaf_315] at hs
  calc w2 315 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (315 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (315 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_315

theorem hpos_leaf_316 : order.symm (490 : Fin 1024) = (316 : Fin 1024) := by decide
#print axioms hpos_leaf_316

theorem w0_leaf_316 : w0 316 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_490 (F := M)
  rw [hpos_leaf_316] at hs
  calc w0 316 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (316 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (316 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_316

theorem w2_leaf_316 : w2 316 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_490 (F := M)
  rw [hpos_leaf_316] at hs
  calc w2 316 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (316 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (316 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_316

theorem hpos_leaf_317 : order.symm (491 : Fin 1024) = (317 : Fin 1024) := by decide
#print axioms hpos_leaf_317

theorem w0_leaf_317 : w0 317 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_491 (F := M)
  rw [hpos_leaf_317] at hs
  calc w0 317 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (317 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (317 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_317

theorem w2_leaf_317 : w2 317 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_491 (F := M)
  rw [hpos_leaf_317] at hs
  calc w2 317 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (317 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (317 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_317

theorem hpos_leaf_318 : order.symm (506 : Fin 1024) = (318 : Fin 1024) := by decide
#print axioms hpos_leaf_318

theorem w0_leaf_318 : w0 318 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_506 (F := M)
  rw [hpos_leaf_318] at hs
  calc w0 318 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (318 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (318 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_318

theorem w2_leaf_318 : w2 318 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_506 (F := M)
  rw [hpos_leaf_318] at hs
  calc w2 318 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (318 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (318 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_318

theorem hpos_leaf_319 : order.symm (507 : Fin 1024) = (319 : Fin 1024) := by decide
#print axioms hpos_leaf_319

theorem w0_leaf_319 : w0 319 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_507 (F := M)
  rw [hpos_leaf_319] at hs
  calc w0 319 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (319 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (319 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_319

theorem w2_leaf_319 : w2 319 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_507 (F := M)
  rw [hpos_leaf_319] at hs
  calc w2 319 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (319 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (319 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_319

theorem hpos_leaf_320 : order.symm (522 : Fin 1024) = (320 : Fin 1024) := by decide
#print axioms hpos_leaf_320

theorem w0_leaf_320 : w0 320 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_522 (F := M)
  rw [hpos_leaf_320] at hs
  calc w0 320 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (320 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (320 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_320

theorem w2_leaf_320 : w2 320 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_522 (F := M)
  rw [hpos_leaf_320] at hs
  calc w2 320 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (320 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (320 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_320

theorem hpos_leaf_321 : order.symm (523 : Fin 1024) = (321 : Fin 1024) := by decide
#print axioms hpos_leaf_321

theorem w0_leaf_321 : w0 321 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_523 (F := M)
  rw [hpos_leaf_321] at hs
  calc w0 321 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (321 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (321 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_321

theorem w2_leaf_321 : w2 321 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_523 (F := M)
  rw [hpos_leaf_321] at hs
  calc w2 321 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (321 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (321 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_321

theorem hpos_leaf_322 : order.symm (538 : Fin 1024) = (322 : Fin 1024) := by decide
#print axioms hpos_leaf_322

theorem w0_leaf_322 : w0 322 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_538 (F := M)
  rw [hpos_leaf_322] at hs
  calc w0 322 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (322 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (322 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_322

theorem w2_leaf_322 : w2 322 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_538 (F := M)
  rw [hpos_leaf_322] at hs
  calc w2 322 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (322 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (322 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_322

theorem hpos_leaf_323 : order.symm (539 : Fin 1024) = (323 : Fin 1024) := by decide
#print axioms hpos_leaf_323

theorem w0_leaf_323 : w0 323 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_539 (F := M)
  rw [hpos_leaf_323] at hs
  calc w0 323 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (323 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (323 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_323

theorem w2_leaf_323 : w2 323 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_539 (F := M)
  rw [hpos_leaf_323] at hs
  calc w2 323 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (323 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (323 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_323

theorem hpos_leaf_324 : order.symm (554 : Fin 1024) = (324 : Fin 1024) := by decide
#print axioms hpos_leaf_324

theorem w0_leaf_324 : w0 324 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_554 (F := M)
  rw [hpos_leaf_324] at hs
  calc w0 324 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (324 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (324 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_324

theorem w2_leaf_324 : w2 324 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_554 (F := M)
  rw [hpos_leaf_324] at hs
  calc w2 324 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (324 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (324 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_324

theorem hpos_leaf_325 : order.symm (555 : Fin 1024) = (325 : Fin 1024) := by decide
#print axioms hpos_leaf_325

theorem w0_leaf_325 : w0 325 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_555 (F := M)
  rw [hpos_leaf_325] at hs
  calc w0 325 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (325 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (325 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_325

theorem w2_leaf_325 : w2 325 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_555 (F := M)
  rw [hpos_leaf_325] at hs
  calc w2 325 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (325 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (325 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_325

theorem hpos_leaf_326 : order.symm (570 : Fin 1024) = (326 : Fin 1024) := by decide
#print axioms hpos_leaf_326

theorem w0_leaf_326 : w0 326 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_570 (F := M)
  rw [hpos_leaf_326] at hs
  calc w0 326 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (326 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (326 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_326

theorem w2_leaf_326 : w2 326 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_570 (F := M)
  rw [hpos_leaf_326] at hs
  calc w2 326 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (326 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (326 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_326

theorem hpos_leaf_327 : order.symm (571 : Fin 1024) = (327 : Fin 1024) := by decide
#print axioms hpos_leaf_327

theorem w0_leaf_327 : w0 327 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_571 (F := M)
  rw [hpos_leaf_327] at hs
  calc w0 327 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (327 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (327 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_327

theorem w2_leaf_327 : w2 327 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_571 (F := M)
  rw [hpos_leaf_327] at hs
  calc w2 327 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (327 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (327 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_327

theorem hpos_leaf_328 : order.symm (586 : Fin 1024) = (328 : Fin 1024) := by decide
#print axioms hpos_leaf_328

theorem w0_leaf_328 : w0 328 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_586 (F := M)
  rw [hpos_leaf_328] at hs
  calc w0 328 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (328 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (328 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_328

theorem w2_leaf_328 : w2 328 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_586 (F := M)
  rw [hpos_leaf_328] at hs
  calc w2 328 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (328 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (328 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_328

theorem hpos_leaf_329 : order.symm (587 : Fin 1024) = (329 : Fin 1024) := by decide
#print axioms hpos_leaf_329

theorem w0_leaf_329 : w0 329 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_587 (F := M)
  rw [hpos_leaf_329] at hs
  calc w0 329 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (329 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (329 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_329

theorem w2_leaf_329 : w2 329 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_587 (F := M)
  rw [hpos_leaf_329] at hs
  calc w2 329 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (329 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (329 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_329

theorem hpos_leaf_330 : order.symm (602 : Fin 1024) = (330 : Fin 1024) := by decide
#print axioms hpos_leaf_330

theorem w0_leaf_330 : w0 330 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_602 (F := M)
  rw [hpos_leaf_330] at hs
  calc w0 330 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (330 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (330 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_330

theorem w2_leaf_330 : w2 330 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_602 (F := M)
  rw [hpos_leaf_330] at hs
  calc w2 330 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (330 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (330 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_330

theorem hpos_leaf_331 : order.symm (603 : Fin 1024) = (331 : Fin 1024) := by decide
#print axioms hpos_leaf_331

theorem w0_leaf_331 : w0 331 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_603 (F := M)
  rw [hpos_leaf_331] at hs
  calc w0 331 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (331 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (331 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_331

theorem w2_leaf_331 : w2 331 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_603 (F := M)
  rw [hpos_leaf_331] at hs
  calc w2 331 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (331 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (331 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_331

theorem hpos_leaf_332 : order.symm (618 : Fin 1024) = (332 : Fin 1024) := by decide
#print axioms hpos_leaf_332

theorem w0_leaf_332 : w0 332 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_618 (F := M)
  rw [hpos_leaf_332] at hs
  calc w0 332 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (332 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (332 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_332

theorem w2_leaf_332 : w2 332 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_618 (F := M)
  rw [hpos_leaf_332] at hs
  calc w2 332 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (332 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (332 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_332

theorem hpos_leaf_333 : order.symm (619 : Fin 1024) = (333 : Fin 1024) := by decide
#print axioms hpos_leaf_333

theorem w0_leaf_333 : w0 333 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p0_transport_zero_original_619 (F := M)
  rw [hpos_leaf_333] at hs
  calc w0 333 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (333 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (333 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_333

theorem w2_leaf_333 : w2 333 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk21.p2_transport_zero_original_619 (F := M)
  rw [hpos_leaf_333] at hs
  calc w2 333 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (333 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (333 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_333

theorem hpos_leaf_334 : order.symm (634 : Fin 1024) = (334 : Fin 1024) := by decide
#print axioms hpos_leaf_334

theorem w0_leaf_334 : w0 334 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p0_transport_zero_original_634 (F := M)
  rw [hpos_leaf_334] at hs
  calc w0 334 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (334 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (334 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_334

theorem w2_leaf_334 : w2 334 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk08.p2_transport_zero_original_634 (F := M)
  rw [hpos_leaf_334] at hs
  calc w2 334 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (334 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (334 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_334

end
end AspisV8R19.R780Point02WeightSharedChunk07
