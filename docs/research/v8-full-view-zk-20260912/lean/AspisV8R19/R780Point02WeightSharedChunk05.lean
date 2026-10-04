import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk05
import AspisV8R19.R772Point02DualLeavesChunk06
import AspisV8R19.R772Point02DualLeavesChunk18
import AspisV8R19.R772Point02DualLeavesChunk19
import AspisV8R19.R772Point02DualLeavesChunk26
import AspisV8R19.R772Point02DualLeavesChunk27
import AspisV8R19.R772Point02DualLeavesChunk29

namespace AspisV8R19.R780Point02WeightSharedChunk05
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_239 : order.symm (893 : Fin 1024) = (239 : Fin 1024) := by decide
#print axioms hpos_leaf_239

theorem w0_leaf_239 : w0 239 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_893 (F := M)
  rw [hpos_leaf_239] at hs
  calc w0 239 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (239 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (239 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_239

theorem w2_leaf_239 : w2 239 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_893 (F := M)
  rw [hpos_leaf_239] at hs
  calc w2 239 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (239 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (239 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_239

theorem hpos_leaf_240 : order.symm (908 : Fin 1024) = (240 : Fin 1024) := by decide
#print axioms hpos_leaf_240

theorem w0_leaf_240 : w0 240 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_908 (F := M)
  rw [hpos_leaf_240] at hs
  calc w0 240 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (240 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (240 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_240

theorem w2_leaf_240 : w2 240 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_908 (F := M)
  rw [hpos_leaf_240] at hs
  calc w2 240 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (240 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (240 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_240

theorem hpos_leaf_241 : order.symm (909 : Fin 1024) = (241 : Fin 1024) := by decide
#print axioms hpos_leaf_241

theorem w0_leaf_241 : w0 241 = ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_909 (F := M)
  rw [hpos_leaf_241] at hs
  calc w0 241 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (241 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (241 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_241

theorem w2_leaf_241 : w2 241 = ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_909 (F := M)
  rw [hpos_leaf_241] at hs
  calc w2 241 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (241 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (241 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_241

theorem hpos_leaf_242 : order.symm (924 : Fin 1024) = (242 : Fin 1024) := by decide
#print axioms hpos_leaf_242

theorem w0_leaf_242 : w0 242 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_924 (F := M)
  rw [hpos_leaf_242] at hs
  calc w0 242 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (242 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (242 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_242

theorem w2_leaf_242 : w2 242 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_924 (F := M)
  rw [hpos_leaf_242] at hs
  calc w2 242 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (242 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (242 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_242

theorem hpos_leaf_243 : order.symm (925 : Fin 1024) = (243 : Fin 1024) := by decide
#print axioms hpos_leaf_243

theorem w0_leaf_243 : w0 243 = ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_925 (F := M)
  rw [hpos_leaf_243] at hs
  calc w0 243 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (243 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (243 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_243

theorem w2_leaf_243 : w2 243 = ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_925 (F := M)
  rw [hpos_leaf_243] at hs
  calc w2 243 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (243 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (243 : Fin 1024))
       _ = ([1, 1, 2, -2, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_243

theorem hpos_leaf_244 : order.symm (940 : Fin 1024) = (244 : Fin 1024) := by decide
#print axioms hpos_leaf_244

theorem w0_leaf_244 : w0 244 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_940 (F := M)
  rw [hpos_leaf_244] at hs
  calc w0 244 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (244 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (244 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_244

theorem w2_leaf_244 : w2 244 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_940 (F := M)
  rw [hpos_leaf_244] at hs
  calc w2 244 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (244 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (244 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_244

theorem hpos_leaf_245 : order.symm (941 : Fin 1024) = (245 : Fin 1024) := by decide
#print axioms hpos_leaf_245

theorem w0_leaf_245 : w0 245 = ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_941 (F := M)
  rw [hpos_leaf_245] at hs
  calc w0 245 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (245 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (245 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_245

theorem w2_leaf_245 : w2 245 = ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_941 (F := M)
  rw [hpos_leaf_245] at hs
  calc w2 245 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (245 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (245 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_245

theorem hpos_leaf_246 : order.symm (956 : Fin 1024) = (246 : Fin 1024) := by decide
#print axioms hpos_leaf_246

theorem w0_leaf_246 : w0 246 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_956 (F := M)
  rw [hpos_leaf_246] at hs
  calc w0 246 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (246 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (246 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_246

theorem w2_leaf_246 : w2 246 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_956 (F := M)
  rw [hpos_leaf_246] at hs
  calc w2 246 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (246 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (246 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_246

theorem hpos_leaf_247 : order.symm (957 : Fin 1024) = (247 : Fin 1024) := by decide
#print axioms hpos_leaf_247

theorem w0_leaf_247 : w0 247 = ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_957 (F := M)
  rw [hpos_leaf_247] at hs
  calc w0 247 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (247 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (247 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_247

theorem w2_leaf_247 : w2 247 = ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_957 (F := M)
  rw [hpos_leaf_247] at hs
  calc w2 247 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (247 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (247 : Fin 1024))
       _ = ([1, 1, 2, -2, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_247

theorem hpos_leaf_248 : order.symm (972 : Fin 1024) = (248 : Fin 1024) := by decide
#print axioms hpos_leaf_248

theorem w0_leaf_248 : w0 248 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_972 (F := M)
  rw [hpos_leaf_248] at hs
  calc w0 248 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (248 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (248 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_248

theorem w2_leaf_248 : w2 248 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_972 (F := M)
  rw [hpos_leaf_248] at hs
  calc w2 248 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (248 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (248 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_248

theorem hpos_leaf_249 : order.symm (973 : Fin 1024) = (249 : Fin 1024) := by decide
#print axioms hpos_leaf_249

theorem w0_leaf_249 : w0 249 = ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_973 (F := M)
  rw [hpos_leaf_249] at hs
  calc w0 249 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (249 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (249 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_249

theorem w2_leaf_249 : w2 249 = ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_973 (F := M)
  rw [hpos_leaf_249] at hs
  calc w2 249 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (249 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (249 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_249

theorem hpos_leaf_250 : order.symm (988 : Fin 1024) = (250 : Fin 1024) := by decide
#print axioms hpos_leaf_250

theorem w0_leaf_250 : w0 250 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_988 (F := M)
  rw [hpos_leaf_250] at hs
  calc w0 250 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (250 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (250 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_250

theorem w2_leaf_250 : w2 250 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_988 (F := M)
  rw [hpos_leaf_250] at hs
  calc w2 250 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (250 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (250 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_250

theorem hpos_leaf_251 : order.symm (989 : Fin 1024) = (251 : Fin 1024) := by decide
#print axioms hpos_leaf_251

theorem w0_leaf_251 : w0 251 = ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_989 (F := M)
  rw [hpos_leaf_251] at hs
  calc w0 251 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (251 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (251 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_251

theorem w2_leaf_251 : w2 251 = ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_989 (F := M)
  rw [hpos_leaf_251] at hs
  calc w2 251 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (251 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (251 : Fin 1024))
       _ = ([1, 1, 2, 3, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_251

theorem hpos_leaf_252 : order.symm (1004 : Fin 1024) = (252 : Fin 1024) := by decide
#print axioms hpos_leaf_252

theorem w0_leaf_252 : w0 252 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_1004 (F := M)
  rw [hpos_leaf_252] at hs
  calc w0 252 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (252 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (252 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_252

theorem w2_leaf_252 : w2 252 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_1004 (F := M)
  rw [hpos_leaf_252] at hs
  calc w2 252 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (252 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (252 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_252

theorem hpos_leaf_253 : order.symm (1005 : Fin 1024) = (253 : Fin 1024) := by decide
#print axioms hpos_leaf_253

theorem w0_leaf_253 : w0 253 = ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p0_transport_exact_original_1005 (F := M)
  rw [hpos_leaf_253] at hs
  calc w0 253 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (253 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (253 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_253

theorem w2_leaf_253 : w2 253 = ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk27.p2_transport_exact_original_1005 (F := M)
  rw [hpos_leaf_253] at hs
  calc w2 253 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (253 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (253 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_253

theorem hpos_leaf_254 : order.symm (1020 : Fin 1024) = (254 : Fin 1024) := by decide
#print axioms hpos_leaf_254

theorem w0_leaf_254 : w0 254 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_1020 (F := M)
  rw [hpos_leaf_254] at hs
  calc w0 254 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (254 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (254 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_254

theorem w2_leaf_254 : w2 254 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_1020 (F := M)
  rw [hpos_leaf_254] at hs
  calc w2 254 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (254 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (254 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_254

theorem hpos_leaf_255 : order.symm (1021 : Fin 1024) = (255 : Fin 1024) := by decide
#print axioms hpos_leaf_255

theorem w0_leaf_255 : w0 255 = ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_1021 (F := M)
  rw [hpos_leaf_255] at hs
  calc w0 255 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (255 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (255 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_255

theorem w2_leaf_255 : w2 255 = ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_1021 (F := M)
  rw [hpos_leaf_255] at hs
  calc w2 255 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (255 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (255 : Fin 1024))
       _ = ([1, 1, 2, 3, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_255

theorem hpos_leaf_256 : order.symm (10 : Fin 1024) = (256 : Fin 1024) := by decide
#print axioms hpos_leaf_256

theorem w0_leaf_256 : w0 256 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_10 (F := M)
  rw [hpos_leaf_256] at hs
  calc w0 256 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (256 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (256 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_256

theorem w2_leaf_256 : w2 256 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_10 (F := M)
  rw [hpos_leaf_256] at hs
  calc w2 256 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (256 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (256 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_256

theorem hpos_leaf_257 : order.symm (11 : Fin 1024) = (257 : Fin 1024) := by decide
#print axioms hpos_leaf_257

theorem w0_leaf_257 : w0 257 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_11 (F := M)
  rw [hpos_leaf_257] at hs
  calc w0 257 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (257 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (257 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_257

theorem w2_leaf_257 : w2 257 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_11 (F := M)
  rw [hpos_leaf_257] at hs
  calc w2 257 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (257 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (257 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_257

theorem hpos_leaf_258 : order.symm (26 : Fin 1024) = (258 : Fin 1024) := by decide
#print axioms hpos_leaf_258

theorem w0_leaf_258 : w0 258 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_26 (F := M)
  rw [hpos_leaf_258] at hs
  calc w0 258 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (258 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (258 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_258

theorem w2_leaf_258 : w2 258 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_26 (F := M)
  rw [hpos_leaf_258] at hs
  calc w2 258 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (258 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (258 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_258

theorem hpos_leaf_259 : order.symm (27 : Fin 1024) = (259 : Fin 1024) := by decide
#print axioms hpos_leaf_259

theorem w0_leaf_259 : w0 259 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_27 (F := M)
  rw [hpos_leaf_259] at hs
  calc w0 259 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (259 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (259 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_259

theorem w2_leaf_259 : w2 259 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_27 (F := M)
  rw [hpos_leaf_259] at hs
  calc w2 259 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (259 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (259 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_259

theorem hpos_leaf_260 : order.symm (42 : Fin 1024) = (260 : Fin 1024) := by decide
#print axioms hpos_leaf_260

theorem w0_leaf_260 : w0 260 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_42 (F := M)
  rw [hpos_leaf_260] at hs
  calc w0 260 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (260 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (260 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_260

theorem w2_leaf_260 : w2 260 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_42 (F := M)
  rw [hpos_leaf_260] at hs
  calc w2 260 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (260 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (260 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_260

theorem hpos_leaf_261 : order.symm (43 : Fin 1024) = (261 : Fin 1024) := by decide
#print axioms hpos_leaf_261

theorem w0_leaf_261 : w0 261 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_43 (F := M)
  rw [hpos_leaf_261] at hs
  calc w0 261 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (261 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (261 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_261

theorem w2_leaf_261 : w2 261 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_43 (F := M)
  rw [hpos_leaf_261] at hs
  calc w2 261 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (261 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (261 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_261

theorem hpos_leaf_262 : order.symm (58 : Fin 1024) = (262 : Fin 1024) := by decide
#print axioms hpos_leaf_262

theorem w0_leaf_262 : w0 262 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_58 (F := M)
  rw [hpos_leaf_262] at hs
  calc w0 262 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (262 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (262 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_262

theorem w2_leaf_262 : w2 262 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_58 (F := M)
  rw [hpos_leaf_262] at hs
  calc w2 262 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (262 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (262 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_262

theorem hpos_leaf_263 : order.symm (59 : Fin 1024) = (263 : Fin 1024) := by decide
#print axioms hpos_leaf_263

theorem w0_leaf_263 : w0 263 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_59 (F := M)
  rw [hpos_leaf_263] at hs
  calc w0 263 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (263 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (263 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_263

theorem w2_leaf_263 : w2 263 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_59 (F := M)
  rw [hpos_leaf_263] at hs
  calc w2 263 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (263 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (263 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_263

theorem hpos_leaf_264 : order.symm (74 : Fin 1024) = (264 : Fin 1024) := by decide
#print axioms hpos_leaf_264

theorem w0_leaf_264 : w0 264 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_74 (F := M)
  rw [hpos_leaf_264] at hs
  calc w0 264 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (264 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (264 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_264

theorem w2_leaf_264 : w2 264 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_74 (F := M)
  rw [hpos_leaf_264] at hs
  calc w2 264 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (264 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (264 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_264

theorem hpos_leaf_265 : order.symm (75 : Fin 1024) = (265 : Fin 1024) := by decide
#print axioms hpos_leaf_265

theorem w0_leaf_265 : w0 265 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_75 (F := M)
  rw [hpos_leaf_265] at hs
  calc w0 265 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (265 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (265 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_265

theorem w2_leaf_265 : w2 265 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_75 (F := M)
  rw [hpos_leaf_265] at hs
  calc w2 265 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (265 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (265 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_265

theorem hpos_leaf_266 : order.symm (90 : Fin 1024) = (266 : Fin 1024) := by decide
#print axioms hpos_leaf_266

theorem w0_leaf_266 : w0 266 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_90 (F := M)
  rw [hpos_leaf_266] at hs
  calc w0 266 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (266 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (266 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_266

theorem w2_leaf_266 : w2 266 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_90 (F := M)
  rw [hpos_leaf_266] at hs
  calc w2 266 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (266 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (266 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_266

theorem hpos_leaf_267 : order.symm (91 : Fin 1024) = (267 : Fin 1024) := by decide
#print axioms hpos_leaf_267

theorem w0_leaf_267 : w0 267 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_91 (F := M)
  rw [hpos_leaf_267] at hs
  calc w0 267 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (267 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (267 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_267

theorem w2_leaf_267 : w2 267 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_91 (F := M)
  rw [hpos_leaf_267] at hs
  calc w2 267 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (267 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (267 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_267

theorem hpos_leaf_268 : order.symm (106 : Fin 1024) = (268 : Fin 1024) := by decide
#print axioms hpos_leaf_268

theorem w0_leaf_268 : w0 268 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_106 (F := M)
  rw [hpos_leaf_268] at hs
  calc w0 268 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (268 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (268 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_268

theorem w2_leaf_268 : w2 268 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_106 (F := M)
  rw [hpos_leaf_268] at hs
  calc w2 268 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (268 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (268 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_268

theorem hpos_leaf_269 : order.symm (107 : Fin 1024) = (269 : Fin 1024) := by decide
#print axioms hpos_leaf_269

theorem w0_leaf_269 : w0 269 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p0_transport_zero_original_107 (F := M)
  rw [hpos_leaf_269] at hs
  calc w0 269 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (269 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (269 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_269

theorem w2_leaf_269 : w2 269 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk19.p2_transport_zero_original_107 (F := M)
  rw [hpos_leaf_269] at hs
  calc w2 269 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (269 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (269 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_269

theorem hpos_leaf_270 : order.symm (122 : Fin 1024) = (270 : Fin 1024) := by decide
#print axioms hpos_leaf_270

theorem w0_leaf_270 : w0 270 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p0_transport_zero_original_122 (F := M)
  rw [hpos_leaf_270] at hs
  calc w0 270 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (270 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (270 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_270

theorem w2_leaf_270 : w2 270 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk06.p2_transport_zero_original_122 (F := M)
  rw [hpos_leaf_270] at hs
  calc w2 270 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (270 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (270 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_270

end
end AspisV8R19.R780Point02WeightSharedChunk05
