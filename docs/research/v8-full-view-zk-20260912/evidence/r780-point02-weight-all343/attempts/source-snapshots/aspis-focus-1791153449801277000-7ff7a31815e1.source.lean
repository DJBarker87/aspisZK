import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeaves
import AspisV8R19.R772Point02DualLeavesChunk05
import AspisV8R19.R772Point02DualLeavesChunk18
import AspisV8R19.R772Point02DualLeavesChunk26
import AspisV8R19.R772Point02DualLeavesChunk28
import AspisV8R19.R772Point02DualLeavesChunk29

namespace AspisV8R19.R780Point02WeightSharedChunk04
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_207 : order.symm (637 : Fin 1024) = (207 : Fin 1024) := by decide
#print axioms hpos_leaf_207

theorem w0_leaf_207 : w0 207 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_637 (F := M)
  rw [hpos_leaf_207] at hs
  calc w0 207 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (207 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (207 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_207

theorem w2_leaf_207 : w2 207 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_637 (F := M)
  rw [hpos_leaf_207] at hs
  calc w2 207 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (207 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (207 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_207

theorem hpos_leaf_208 : order.symm (652 : Fin 1024) = (208 : Fin 1024) := by decide
#print axioms hpos_leaf_208

theorem w0_leaf_208 : w0 208 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_652 (F := M)
  rw [hpos_leaf_208] at hs
  calc w0 208 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (208 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (208 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_208

theorem w2_leaf_208 : w2 208 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_652 (F := M)
  rw [hpos_leaf_208] at hs
  calc w2 208 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (208 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (208 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_208

theorem hpos_leaf_209 : order.symm (653 : Fin 1024) = (209 : Fin 1024) := by decide
#print axioms hpos_leaf_209

theorem w0_leaf_209 : w0 209 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_653 (F := M)
  rw [hpos_leaf_209] at hs
  calc w0 209 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (209 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (209 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_209

theorem w2_leaf_209 : w2 209 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_653 (F := M)
  rw [hpos_leaf_209] at hs
  calc w2 209 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (209 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (209 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_209

theorem hpos_leaf_210 : order.symm (668 : Fin 1024) = (210 : Fin 1024) := by decide
#print axioms hpos_leaf_210

theorem w0_leaf_210 : w0 210 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_668 (F := M)
  rw [hpos_leaf_210] at hs
  calc w0 210 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (210 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (210 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_210

theorem w2_leaf_210 : w2 210 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_668 (F := M)
  rw [hpos_leaf_210] at hs
  calc w2 210 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (210 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (210 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_210

theorem hpos_leaf_211 : order.symm (669 : Fin 1024) = (211 : Fin 1024) := by decide
#print axioms hpos_leaf_211

theorem w0_leaf_211 : w0 211 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_669 (F := M)
  rw [hpos_leaf_211] at hs
  calc w0 211 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (211 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (211 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_211

theorem w2_leaf_211 : w2 211 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_669 (F := M)
  rw [hpos_leaf_211] at hs
  calc w2 211 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (211 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (211 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_211

theorem hpos_leaf_212 : order.symm (684 : Fin 1024) = (212 : Fin 1024) := by decide
#print axioms hpos_leaf_212

theorem w0_leaf_212 : w0 212 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_684 (F := M)
  rw [hpos_leaf_212] at hs
  calc w0 212 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (212 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (212 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_212

theorem w2_leaf_212 : w2 212 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_684 (F := M)
  rw [hpos_leaf_212] at hs
  calc w2 212 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (212 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (212 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_212

theorem hpos_leaf_213 : order.symm (685 : Fin 1024) = (213 : Fin 1024) := by decide
#print axioms hpos_leaf_213

theorem w0_leaf_213 : w0 213 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_685 (F := M)
  rw [hpos_leaf_213] at hs
  calc w0 213 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (213 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (213 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_213

theorem w2_leaf_213 : w2 213 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_685 (F := M)
  rw [hpos_leaf_213] at hs
  calc w2 213 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (213 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (213 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_213

theorem hpos_leaf_214 : order.symm (700 : Fin 1024) = (214 : Fin 1024) := by decide
#print axioms hpos_leaf_214

theorem w0_leaf_214 : w0 214 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_700 (F := M)
  rw [hpos_leaf_214] at hs
  calc w0 214 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (214 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (214 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_214

theorem w2_leaf_214 : w2 214 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_700 (F := M)
  rw [hpos_leaf_214] at hs
  calc w2 214 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (214 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (214 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_214

theorem hpos_leaf_215 : order.symm (701 : Fin 1024) = (215 : Fin 1024) := by decide
#print axioms hpos_leaf_215

theorem w0_leaf_215 : w0 215 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_701 (F := M)
  rw [hpos_leaf_215] at hs
  calc w0 215 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (215 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (215 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_215

theorem w2_leaf_215 : w2 215 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_701 (F := M)
  rw [hpos_leaf_215] at hs
  calc w2 215 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (215 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (215 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_215

theorem hpos_leaf_216 : order.symm (716 : Fin 1024) = (216 : Fin 1024) := by decide
#print axioms hpos_leaf_216

theorem w0_leaf_216 : w0 216 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_716 (F := M)
  rw [hpos_leaf_216] at hs
  calc w0 216 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (216 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (216 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_216

theorem w2_leaf_216 : w2 216 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_716 (F := M)
  rw [hpos_leaf_216] at hs
  calc w2 216 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (216 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (216 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_216

theorem hpos_leaf_217 : order.symm (717 : Fin 1024) = (217 : Fin 1024) := by decide
#print axioms hpos_leaf_217

theorem w0_leaf_217 : w0 217 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_717 (F := M)
  rw [hpos_leaf_217] at hs
  calc w0 217 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (217 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (217 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_217

theorem w2_leaf_217 : w2 217 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_717 (F := M)
  rw [hpos_leaf_217] at hs
  calc w2 217 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (217 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (217 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_217

theorem hpos_leaf_218 : order.symm (732 : Fin 1024) = (218 : Fin 1024) := by decide
#print axioms hpos_leaf_218

theorem w0_leaf_218 : w0 218 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_732 (F := M)
  rw [hpos_leaf_218] at hs
  calc w0 218 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (218 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (218 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_218

theorem w2_leaf_218 : w2 218 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_732 (F := M)
  rw [hpos_leaf_218] at hs
  calc w2 218 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (218 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (218 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_218

theorem hpos_leaf_219 : order.symm (733 : Fin 1024) = (219 : Fin 1024) := by decide
#print axioms hpos_leaf_219

theorem w0_leaf_219 : w0 219 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_733 (F := M)
  rw [hpos_leaf_219] at hs
  calc w0 219 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (219 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (219 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_219

theorem w2_leaf_219 : w2 219 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_733 (F := M)
  rw [hpos_leaf_219] at hs
  calc w2 219 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (219 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (219 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_219

theorem hpos_leaf_220 : order.symm (748 : Fin 1024) = (220 : Fin 1024) := by decide
#print axioms hpos_leaf_220

theorem w0_leaf_220 : w0 220 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_748 (F := M)
  rw [hpos_leaf_220] at hs
  calc w0 220 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (220 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (220 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_220

theorem w2_leaf_220 : w2 220 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_748 (F := M)
  rw [hpos_leaf_220] at hs
  calc w2 220 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (220 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (220 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_220

theorem hpos_leaf_221 : order.symm (749 : Fin 1024) = (221 : Fin 1024) := by decide
#print axioms hpos_leaf_221

theorem w0_leaf_221 : w0 221 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_749 (F := M)
  rw [hpos_leaf_221] at hs
  calc w0 221 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (221 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (221 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_221

theorem w2_leaf_221 : w2 221 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_749 (F := M)
  rw [hpos_leaf_221] at hs
  calc w2 221 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (221 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (221 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_221

theorem hpos_leaf_222 : order.symm (764 : Fin 1024) = (222 : Fin 1024) := by decide
#print axioms hpos_leaf_222

theorem w0_leaf_222 : w0 222 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_764 (F := M)
  rw [hpos_leaf_222] at hs
  calc w0 222 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (222 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (222 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_222

theorem w2_leaf_222 : w2 222 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_764 (F := M)
  rw [hpos_leaf_222] at hs
  calc w2 222 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (222 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (222 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_222

theorem hpos_leaf_223 : order.symm (765 : Fin 1024) = (223 : Fin 1024) := by decide
#print axioms hpos_leaf_223

theorem w0_leaf_223 : w0 223 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_765 (F := M)
  rw [hpos_leaf_223] at hs
  calc w0 223 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (223 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (223 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_223

theorem w2_leaf_223 : w2 223 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_765 (F := M)
  rw [hpos_leaf_223] at hs
  calc w2 223 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (223 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (223 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_223

theorem hpos_leaf_224 : order.symm (780 : Fin 1024) = (224 : Fin 1024) := by decide
#print axioms hpos_leaf_224

theorem w0_leaf_224 : w0 224 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeaves.point0_candidate780_transport_exact (F := M)
  rw [hpos_leaf_224] at hs
  calc w0 224 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (224 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (224 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_224

theorem w2_leaf_224 : w2 224 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeaves.point2_candidate780_transport_exact (F := M)
  rw [hpos_leaf_224] at hs
  calc w2 224 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (224 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (224 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_224

theorem hpos_leaf_225 : order.symm (781 : Fin 1024) = (225 : Fin 1024) := by decide
#print axioms hpos_leaf_225

theorem w0_leaf_225 : w0 225 = ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p0_transport_exact_original_781 (F := M)
  rw [hpos_leaf_225] at hs
  calc w0 225 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (225 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (225 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_225

theorem w2_leaf_225 : w2 225 = ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk28.p2_transport_exact_original_781 (F := M)
  rw [hpos_leaf_225] at hs
  calc w2 225 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (225 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (225 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_225

theorem hpos_leaf_226 : order.symm (796 : Fin 1024) = (226 : Fin 1024) := by decide
#print axioms hpos_leaf_226

theorem w0_leaf_226 : w0 226 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_796 (F := M)
  rw [hpos_leaf_226] at hs
  calc w0 226 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (226 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (226 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_226

theorem w2_leaf_226 : w2 226 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_796 (F := M)
  rw [hpos_leaf_226] at hs
  calc w2 226 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (226 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (226 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_226

theorem hpos_leaf_227 : order.symm (797 : Fin 1024) = (227 : Fin 1024) := by decide
#print axioms hpos_leaf_227

theorem w0_leaf_227 : w0 227 = ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_797 (F := M)
  rw [hpos_leaf_227] at hs
  calc w0 227 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (227 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (227 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_227

theorem w2_leaf_227 : w2 227 = ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_797 (F := M)
  rw [hpos_leaf_227] at hs
  calc w2 227 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (227 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (227 : Fin 1024))
       _ = ([1, 1, -1, -2, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_227

theorem hpos_leaf_228 : order.symm (812 : Fin 1024) = (228 : Fin 1024) := by decide
#print axioms hpos_leaf_228

theorem w0_leaf_228 : w0 228 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_812 (F := M)
  rw [hpos_leaf_228] at hs
  calc w0 228 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (228 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (228 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_228

theorem w2_leaf_228 : w2 228 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_812 (F := M)
  rw [hpos_leaf_228] at hs
  calc w2 228 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (228 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (228 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_228

theorem hpos_leaf_229 : order.symm (813 : Fin 1024) = (229 : Fin 1024) := by decide
#print axioms hpos_leaf_229

theorem w0_leaf_229 : w0 229 = ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_813 (F := M)
  rw [hpos_leaf_229] at hs
  calc w0 229 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (229 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (229 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_229

theorem w2_leaf_229 : w2 229 = ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_813 (F := M)
  rw [hpos_leaf_229] at hs
  calc w2 229 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (229 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (229 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_229

theorem hpos_leaf_230 : order.symm (828 : Fin 1024) = (230 : Fin 1024) := by decide
#print axioms hpos_leaf_230

theorem w0_leaf_230 : w0 230 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_828 (F := M)
  rw [hpos_leaf_230] at hs
  calc w0 230 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (230 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (230 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_230

theorem w2_leaf_230 : w2 230 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_828 (F := M)
  rw [hpos_leaf_230] at hs
  calc w2 230 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (230 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (230 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_230

theorem hpos_leaf_231 : order.symm (829 : Fin 1024) = (231 : Fin 1024) := by decide
#print axioms hpos_leaf_231

theorem w0_leaf_231 : w0 231 = ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_829 (F := M)
  rw [hpos_leaf_231] at hs
  calc w0 231 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (231 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (231 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_231

theorem w2_leaf_231 : w2 231 = ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_829 (F := M)
  rw [hpos_leaf_231] at hs
  calc w2 231 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (231 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (231 : Fin 1024))
       _ = ([1, 1, -1, -2, 4, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_231

theorem hpos_leaf_232 : order.symm (844 : Fin 1024) = (232 : Fin 1024) := by decide
#print axioms hpos_leaf_232

theorem w0_leaf_232 : w0 232 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_844 (F := M)
  rw [hpos_leaf_232] at hs
  calc w0 232 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (232 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (232 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_232

theorem w2_leaf_232 : w2 232 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_844 (F := M)
  rw [hpos_leaf_232] at hs
  calc w2 232 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (232 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (232 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_232

theorem hpos_leaf_233 : order.symm (845 : Fin 1024) = (233 : Fin 1024) := by decide
#print axioms hpos_leaf_233

theorem w0_leaf_233 : w0 233 = ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_845 (F := M)
  rw [hpos_leaf_233] at hs
  calc w0 233 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (233 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (233 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_233

theorem w2_leaf_233 : w2 233 = ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_845 (F := M)
  rw [hpos_leaf_233] at hs
  calc w2 233 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (233 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (233 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_233

theorem hpos_leaf_234 : order.symm (860 : Fin 1024) = (234 : Fin 1024) := by decide
#print axioms hpos_leaf_234

theorem w0_leaf_234 : w0 234 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_860 (F := M)
  rw [hpos_leaf_234] at hs
  calc w0 234 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (234 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (234 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_234

theorem w2_leaf_234 : w2 234 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_860 (F := M)
  rw [hpos_leaf_234] at hs
  calc w2 234 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (234 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (234 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_234

theorem hpos_leaf_235 : order.symm (861 : Fin 1024) = (235 : Fin 1024) := by decide
#print axioms hpos_leaf_235

theorem w0_leaf_235 : w0 235 = ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_861 (F := M)
  rw [hpos_leaf_235] at hs
  calc w0 235 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (235 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (235 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_235

theorem w2_leaf_235 : w2 235 = ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_861 (F := M)
  rw [hpos_leaf_235] at hs
  calc w2 235 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (235 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (235 : Fin 1024))
       _ = ([1, 1, -1, 3, -3, 2, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_235

theorem hpos_leaf_236 : order.symm (876 : Fin 1024) = (236 : Fin 1024) := by decide
#print axioms hpos_leaf_236

theorem w0_leaf_236 : w0 236 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_876 (F := M)
  rw [hpos_leaf_236] at hs
  calc w0 236 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (236 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (236 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_236

theorem w2_leaf_236 : w2 236 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_876 (F := M)
  rw [hpos_leaf_236] at hs
  calc w2 236 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (236 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (236 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_236

theorem hpos_leaf_237 : order.symm (877 : Fin 1024) = (237 : Fin 1024) := by decide
#print axioms hpos_leaf_237

theorem w0_leaf_237 : w0 237 = ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p0_transport_exact_original_877 (F := M)
  rw [hpos_leaf_237] at hs
  calc w0 237 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (237 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (237 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, 2, 3, 1, 2] : List M).prod := hs

#print axioms w0_leaf_237

theorem w2_leaf_237 : w2 237 = ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk29.p2_transport_exact_original_877 (F := M)
  rw [hpos_leaf_237] at hs
  calc w2 237 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (237 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (237 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, -1, -1, -2, 1, 2] : List M).prod := hs

#print axioms w2_leaf_237

theorem hpos_leaf_238 : order.symm (892 : Fin 1024) = (238 : Fin 1024) := by decide
#print axioms hpos_leaf_238

theorem w0_leaf_238 : w0 238 = ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p0_transport_exact_original_892 (F := M)
  rw [hpos_leaf_238] at hs
  calc w0 238 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (238 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (238 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, 2, 3, 1, -1] : List M).prod := hs

#print axioms w0_leaf_238

theorem w2_leaf_238 : w2 238 = ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk26.p2_transport_exact_original_892 (F := M)
  rw [hpos_leaf_238] at hs
  calc w2 238 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (238 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (238 : Fin 1024))
       _ = ([1, 1, -1, 3, 4, 2, -1, -2, 1, -1] : List M).prod := hs

#print axioms w2_leaf_238

end
end AspisV8R19.R780Point02WeightSharedChunk04
