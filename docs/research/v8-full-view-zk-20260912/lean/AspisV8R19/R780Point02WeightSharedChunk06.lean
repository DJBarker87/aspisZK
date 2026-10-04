import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk06
import AspisV8R19.R772Point02DualLeavesChunk07
import AspisV8R19.R772Point02DualLeavesChunk19
import AspisV8R19.R772Point02DualLeavesChunk20

namespace AspisV8R19.R780Point02WeightSharedChunk06
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_271 : order.symm (123 : Fin 1024) = (271 : Fin 1024) := by decide
#print axioms hpos_leaf_271

theorem w0_leaf_271 : w0 271 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_123 (F := M)
  rw [hpos_leaf_271] at hs
  calc w0 271 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (271 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (271 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_271

theorem w2_leaf_271 : w2 271 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_123 (F := M)
  rw [hpos_leaf_271] at hs
  calc w2 271 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (271 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (271 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_271

theorem hpos_leaf_272 : order.symm (138 : Fin 1024) = (272 : Fin 1024) := by decide
#print axioms hpos_leaf_272

theorem w0_leaf_272 : w0 272 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_138 (F := M)
  rw [hpos_leaf_272] at hs
  calc w0 272 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (272 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (272 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_272

theorem w2_leaf_272 : w2 272 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_138 (F := M)
  rw [hpos_leaf_272] at hs
  calc w2 272 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (272 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (272 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_272

theorem hpos_leaf_273 : order.symm (139 : Fin 1024) = (273 : Fin 1024) := by decide
#print axioms hpos_leaf_273

theorem w0_leaf_273 : w0 273 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_139 (F := M)
  rw [hpos_leaf_273] at hs
  calc w0 273 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (273 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (273 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_273

theorem w2_leaf_273 : w2 273 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_139 (F := M)
  rw [hpos_leaf_273] at hs
  calc w2 273 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (273 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (273 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_273

theorem hpos_leaf_274 : order.symm (154 : Fin 1024) = (274 : Fin 1024) := by decide
#print axioms hpos_leaf_274

theorem w0_leaf_274 : w0 274 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_154 (F := M)
  rw [hpos_leaf_274] at hs
  calc w0 274 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (274 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (274 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_274

theorem w2_leaf_274 : w2 274 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_154 (F := M)
  rw [hpos_leaf_274] at hs
  calc w2 274 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (274 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (274 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_274

theorem hpos_leaf_275 : order.symm (155 : Fin 1024) = (275 : Fin 1024) := by decide
#print axioms hpos_leaf_275

theorem w0_leaf_275 : w0 275 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_155 (F := M)
  rw [hpos_leaf_275] at hs
  calc w0 275 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (275 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (275 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_275

theorem w2_leaf_275 : w2 275 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_155 (F := M)
  rw [hpos_leaf_275] at hs
  calc w2 275 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (275 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (275 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_275

theorem hpos_leaf_276 : order.symm (170 : Fin 1024) = (276 : Fin 1024) := by decide
#print axioms hpos_leaf_276

theorem w0_leaf_276 : w0 276 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_170 (F := M)
  rw [hpos_leaf_276] at hs
  calc w0 276 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (276 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (276 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_276

theorem w2_leaf_276 : w2 276 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_170 (F := M)
  rw [hpos_leaf_276] at hs
  calc w2 276 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (276 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (276 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_276

theorem hpos_leaf_277 : order.symm (171 : Fin 1024) = (277 : Fin 1024) := by decide
#print axioms hpos_leaf_277

theorem w0_leaf_277 : w0 277 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_171 (F := M)
  rw [hpos_leaf_277] at hs
  calc w0 277 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (277 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (277 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_277

theorem w2_leaf_277 : w2 277 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_171 (F := M)
  rw [hpos_leaf_277] at hs
  calc w2 277 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (277 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (277 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_277

theorem hpos_leaf_278 : order.symm (186 : Fin 1024) = (278 : Fin 1024) := by decide
#print axioms hpos_leaf_278

theorem w0_leaf_278 : w0 278 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_186 (F := M)
  rw [hpos_leaf_278] at hs
  calc w0 278 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (278 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (278 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_278

theorem w2_leaf_278 : w2 278 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_186 (F := M)
  rw [hpos_leaf_278] at hs
  calc w2 278 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (278 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (278 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_278

theorem hpos_leaf_279 : order.symm (187 : Fin 1024) = (279 : Fin 1024) := by decide
#print axioms hpos_leaf_279

theorem w0_leaf_279 : w0 279 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_187 (F := M)
  rw [hpos_leaf_279] at hs
  calc w0 279 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (279 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (279 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_279

theorem w2_leaf_279 : w2 279 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_187 (F := M)
  rw [hpos_leaf_279] at hs
  calc w2 279 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (279 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (279 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_279

theorem hpos_leaf_280 : order.symm (202 : Fin 1024) = (280 : Fin 1024) := by decide
#print axioms hpos_leaf_280

theorem w0_leaf_280 : w0 280 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_202 (F := M)
  rw [hpos_leaf_280] at hs
  calc w0 280 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (280 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (280 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_280

theorem w2_leaf_280 : w2 280 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_202 (F := M)
  rw [hpos_leaf_280] at hs
  calc w2 280 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (280 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (280 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_280

theorem hpos_leaf_281 : order.symm (203 : Fin 1024) = (281 : Fin 1024) := by decide
#print axioms hpos_leaf_281

theorem w0_leaf_281 : w0 281 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_203 (F := M)
  rw [hpos_leaf_281] at hs
  calc w0 281 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (281 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (281 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_281

theorem w2_leaf_281 : w2 281 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_203 (F := M)
  rw [hpos_leaf_281] at hs
  calc w2 281 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (281 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (281 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_281

theorem hpos_leaf_282 : order.symm (218 : Fin 1024) = (282 : Fin 1024) := by decide
#print axioms hpos_leaf_282

theorem w0_leaf_282 : w0 282 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_218 (F := M)
  rw [hpos_leaf_282] at hs
  calc w0 282 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (282 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (282 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_282

theorem w2_leaf_282 : w2 282 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_218 (F := M)
  rw [hpos_leaf_282] at hs
  calc w2 282 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (282 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (282 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_282

theorem hpos_leaf_283 : order.symm (219 : Fin 1024) = (283 : Fin 1024) := by decide
#print axioms hpos_leaf_283

theorem w0_leaf_283 : w0 283 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_219 (F := M)
  rw [hpos_leaf_283] at hs
  calc w0 283 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (283 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (283 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_283

theorem w2_leaf_283 : w2 283 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_219 (F := M)
  rw [hpos_leaf_283] at hs
  calc w2 283 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (283 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (283 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_283

theorem hpos_leaf_284 : order.symm (234 : Fin 1024) = (284 : Fin 1024) := by decide
#print axioms hpos_leaf_284

theorem w0_leaf_284 : w0 284 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_234 (F := M)
  rw [hpos_leaf_284] at hs
  calc w0 284 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (284 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (284 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_284

theorem w2_leaf_284 : w2 284 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_234 (F := M)
  rw [hpos_leaf_284] at hs
  calc w2 284 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (284 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (284 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_284

theorem hpos_leaf_285 : order.symm (235 : Fin 1024) = (285 : Fin 1024) := by decide
#print axioms hpos_leaf_285

theorem w0_leaf_285 : w0 285 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_235 (F := M)
  rw [hpos_leaf_285] at hs
  calc w0 285 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (285 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (285 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_285

theorem w2_leaf_285 : w2 285 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_235 (F := M)
  rw [hpos_leaf_285] at hs
  calc w2 285 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (285 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (285 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_285

theorem hpos_leaf_286 : order.symm (250 : Fin 1024) = (286 : Fin 1024) := by decide
#print axioms hpos_leaf_286

theorem w0_leaf_286 : w0 286 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_250 (F := M)
  rw [hpos_leaf_286] at hs
  calc w0 286 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (286 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (286 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_286

theorem w2_leaf_286 : w2 286 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_250 (F := M)
  rw [hpos_leaf_286] at hs
  calc w2 286 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (286 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (286 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_286

theorem hpos_leaf_287 : order.symm (251 : Fin 1024) = (287 : Fin 1024) := by decide
#print axioms hpos_leaf_287

theorem w0_leaf_287 : w0 287 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_251 (F := M)
  rw [hpos_leaf_287] at hs
  calc w0 287 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (287 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (287 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_287

theorem w2_leaf_287 : w2 287 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_251 (F := M)
  rw [hpos_leaf_287] at hs
  calc w2 287 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (287 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (287 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_287

theorem hpos_leaf_288 : order.symm (266 : Fin 1024) = (288 : Fin 1024) := by decide
#print axioms hpos_leaf_288

theorem w0_leaf_288 : w0 288 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_266 (F := M)
  rw [hpos_leaf_288] at hs
  calc w0 288 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (288 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (288 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_288

theorem w2_leaf_288 : w2 288 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_266 (F := M)
  rw [hpos_leaf_288] at hs
  calc w2 288 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (288 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (288 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_288

theorem hpos_leaf_289 : order.symm (267 : Fin 1024) = (289 : Fin 1024) := by decide
#print axioms hpos_leaf_289

theorem w0_leaf_289 : w0 289 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_267 (F := M)
  rw [hpos_leaf_289] at hs
  calc w0 289 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (289 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (289 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_289

theorem w2_leaf_289 : w2 289 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_267 (F := M)
  rw [hpos_leaf_289] at hs
  calc w2 289 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (289 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (289 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_289

theorem hpos_leaf_290 : order.symm (282 : Fin 1024) = (290 : Fin 1024) := by decide
#print axioms hpos_leaf_290

theorem w0_leaf_290 : w0 290 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_282 (F := M)
  rw [hpos_leaf_290] at hs
  calc w0 290 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (290 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (290 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_290

theorem w2_leaf_290 : w2 290 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_282 (F := M)
  rw [hpos_leaf_290] at hs
  calc w2 290 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (290 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (290 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_290

theorem hpos_leaf_291 : order.symm (283 : Fin 1024) = (291 : Fin 1024) := by decide
#print axioms hpos_leaf_291

theorem w0_leaf_291 : w0 291 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_283 (F := M)
  rw [hpos_leaf_291] at hs
  calc w0 291 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (291 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (291 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_291

theorem w2_leaf_291 : w2 291 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_283 (F := M)
  rw [hpos_leaf_291] at hs
  calc w2 291 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (291 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (291 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_291

theorem hpos_leaf_292 : order.symm (298 : Fin 1024) = (292 : Fin 1024) := by decide
#print axioms hpos_leaf_292

theorem w0_leaf_292 : w0 292 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_298 (F := M)
  rw [hpos_leaf_292] at hs
  calc w0 292 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (292 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (292 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_292

theorem w2_leaf_292 : w2 292 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_298 (F := M)
  rw [hpos_leaf_292] at hs
  calc w2 292 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (292 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (292 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_292

theorem hpos_leaf_293 : order.symm (299 : Fin 1024) = (293 : Fin 1024) := by decide
#print axioms hpos_leaf_293

theorem w0_leaf_293 : w0 293 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_299 (F := M)
  rw [hpos_leaf_293] at hs
  calc w0 293 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (293 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (293 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_293

theorem w2_leaf_293 : w2 293 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_299 (F := M)
  rw [hpos_leaf_293] at hs
  calc w2 293 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (293 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (293 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_293

theorem hpos_leaf_294 : order.symm (314 : Fin 1024) = (294 : Fin 1024) := by decide
#print axioms hpos_leaf_294

theorem w0_leaf_294 : w0 294 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_314 (F := M)
  rw [hpos_leaf_294] at hs
  calc w0 294 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (294 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (294 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_294

theorem w2_leaf_294 : w2 294 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_314 (F := M)
  rw [hpos_leaf_294] at hs
  calc w2 294 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (294 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (294 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_294

theorem hpos_leaf_295 : order.symm (315 : Fin 1024) = (295 : Fin 1024) := by decide
#print axioms hpos_leaf_295

theorem w0_leaf_295 : w0 295 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_315 (F := M)
  rw [hpos_leaf_295] at hs
  calc w0 295 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (295 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (295 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_295

theorem w2_leaf_295 : w2 295 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_315 (F := M)
  rw [hpos_leaf_295] at hs
  calc w2 295 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (295 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (295 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_295

theorem hpos_leaf_296 : order.symm (330 : Fin 1024) = (296 : Fin 1024) := by decide
#print axioms hpos_leaf_296

theorem w0_leaf_296 : w0 296 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_330 (F := M)
  rw [hpos_leaf_296] at hs
  calc w0 296 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (296 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (296 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_296

theorem w2_leaf_296 : w2 296 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_330 (F := M)
  rw [hpos_leaf_296] at hs
  calc w2 296 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (296 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (296 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_296

theorem hpos_leaf_297 : order.symm (331 : Fin 1024) = (297 : Fin 1024) := by decide
#print axioms hpos_leaf_297

theorem w0_leaf_297 : w0 297 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_331 (F := M)
  rw [hpos_leaf_297] at hs
  calc w0 297 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (297 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (297 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_297

theorem w2_leaf_297 : w2 297 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_331 (F := M)
  rw [hpos_leaf_297] at hs
  calc w2 297 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (297 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (297 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_297

theorem hpos_leaf_298 : order.symm (346 : Fin 1024) = (298 : Fin 1024) := by decide
#print axioms hpos_leaf_298

theorem w0_leaf_298 : w0 298 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_346 (F := M)
  rw [hpos_leaf_298] at hs
  calc w0 298 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (298 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (298 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_298

theorem w2_leaf_298 : w2 298 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_346 (F := M)
  rw [hpos_leaf_298] at hs
  calc w2 298 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (298 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (298 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_298

theorem hpos_leaf_299 : order.symm (347 : Fin 1024) = (299 : Fin 1024) := by decide
#print axioms hpos_leaf_299

theorem w0_leaf_299 : w0 299 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_347 (F := M)
  rw [hpos_leaf_299] at hs
  calc w0 299 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (299 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (299 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_299

theorem w2_leaf_299 : w2 299 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_347 (F := M)
  rw [hpos_leaf_299] at hs
  calc w2 299 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (299 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (299 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_299

theorem hpos_leaf_300 : order.symm (362 : Fin 1024) = (300 : Fin 1024) := by decide
#print axioms hpos_leaf_300

theorem w0_leaf_300 : w0 300 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_362 (F := M)
  rw [hpos_leaf_300] at hs
  calc w0 300 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (300 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (300 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_300

theorem w2_leaf_300 : w2 300 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_362 (F := M)
  rw [hpos_leaf_300] at hs
  calc w2 300 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (300 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (300 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_300

theorem hpos_leaf_301 : order.symm (363 : Fin 1024) = (301 : Fin 1024) := by decide
#print axioms hpos_leaf_301

theorem w0_leaf_301 : w0 301 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p0_transport_zero_original_363 (F := M)
  rw [hpos_leaf_301] at hs
  calc w0 301 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (301 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (301 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_301

theorem w2_leaf_301 : w2 301 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk20.p2_transport_zero_original_363 (F := M)
  rw [hpos_leaf_301] at hs
  calc w2 301 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (301 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (301 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_301

theorem hpos_leaf_302 : order.symm (378 : Fin 1024) = (302 : Fin 1024) := by decide
#print axioms hpos_leaf_302

theorem w0_leaf_302 : w0 302 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p0_transport_zero_original_378 (F := M)
  rw [hpos_leaf_302] at hs
  calc w0 302 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (302 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (302 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_302

theorem w2_leaf_302 : w2 302 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk07.p2_transport_zero_original_378 (F := M)
  rw [hpos_leaf_302] at hs
  calc w2 302 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (302 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (302 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_302

end
end AspisV8R19.R780Point02WeightSharedChunk06
