import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk03
import AspisV8R19.R772Point02DualLeavesChunk04
import AspisV8R19.R772Point02DualLeavesChunk05
import AspisV8R19.R772Point02DualLeavesChunk17
import AspisV8R19.R772Point02DualLeavesChunk18

namespace AspisV8R19.R780Point02WeightSharedChunk03
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_175 : order.symm (381 : Fin 1024) = (175 : Fin 1024) := by decide
#print axioms hpos_leaf_175

theorem w0_leaf_175 : w0 175 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_381 (F := M)
  rw [hpos_leaf_175] at hs
  calc w0 175 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (175 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (175 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_175

theorem w2_leaf_175 : w2 175 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_381 (F := M)
  rw [hpos_leaf_175] at hs
  calc w2 175 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (175 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (175 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_175

theorem hpos_leaf_176 : order.symm (396 : Fin 1024) = (176 : Fin 1024) := by decide
#print axioms hpos_leaf_176

theorem w0_leaf_176 : w0 176 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_396 (F := M)
  rw [hpos_leaf_176] at hs
  calc w0 176 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (176 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (176 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_176

theorem w2_leaf_176 : w2 176 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_396 (F := M)
  rw [hpos_leaf_176] at hs
  calc w2 176 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (176 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (176 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_176

theorem hpos_leaf_177 : order.symm (397 : Fin 1024) = (177 : Fin 1024) := by decide
#print axioms hpos_leaf_177

theorem w0_leaf_177 : w0 177 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_397 (F := M)
  rw [hpos_leaf_177] at hs
  calc w0 177 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (177 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (177 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_177

theorem w2_leaf_177 : w2 177 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_397 (F := M)
  rw [hpos_leaf_177] at hs
  calc w2 177 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (177 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (177 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_177

theorem hpos_leaf_178 : order.symm (412 : Fin 1024) = (178 : Fin 1024) := by decide
#print axioms hpos_leaf_178

theorem w0_leaf_178 : w0 178 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_412 (F := M)
  rw [hpos_leaf_178] at hs
  calc w0 178 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (178 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (178 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_178

theorem w2_leaf_178 : w2 178 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_412 (F := M)
  rw [hpos_leaf_178] at hs
  calc w2 178 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (178 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (178 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_178

theorem hpos_leaf_179 : order.symm (413 : Fin 1024) = (179 : Fin 1024) := by decide
#print axioms hpos_leaf_179

theorem w0_leaf_179 : w0 179 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_413 (F := M)
  rw [hpos_leaf_179] at hs
  calc w0 179 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (179 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (179 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_179

theorem w2_leaf_179 : w2 179 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_413 (F := M)
  rw [hpos_leaf_179] at hs
  calc w2 179 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (179 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (179 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_179

theorem hpos_leaf_180 : order.symm (428 : Fin 1024) = (180 : Fin 1024) := by decide
#print axioms hpos_leaf_180

theorem w0_leaf_180 : w0 180 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_428 (F := M)
  rw [hpos_leaf_180] at hs
  calc w0 180 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (180 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (180 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_180

theorem w2_leaf_180 : w2 180 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_428 (F := M)
  rw [hpos_leaf_180] at hs
  calc w2 180 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (180 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (180 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_180

theorem hpos_leaf_181 : order.symm (429 : Fin 1024) = (181 : Fin 1024) := by decide
#print axioms hpos_leaf_181

theorem w0_leaf_181 : w0 181 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_429 (F := M)
  rw [hpos_leaf_181] at hs
  calc w0 181 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (181 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (181 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_181

theorem w2_leaf_181 : w2 181 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_429 (F := M)
  rw [hpos_leaf_181] at hs
  calc w2 181 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (181 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (181 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_181

theorem hpos_leaf_182 : order.symm (444 : Fin 1024) = (182 : Fin 1024) := by decide
#print axioms hpos_leaf_182

theorem w0_leaf_182 : w0 182 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_444 (F := M)
  rw [hpos_leaf_182] at hs
  calc w0 182 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (182 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (182 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_182

theorem w2_leaf_182 : w2 182 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_444 (F := M)
  rw [hpos_leaf_182] at hs
  calc w2 182 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (182 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (182 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_182

theorem hpos_leaf_183 : order.symm (445 : Fin 1024) = (183 : Fin 1024) := by decide
#print axioms hpos_leaf_183

theorem w0_leaf_183 : w0 183 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_445 (F := M)
  rw [hpos_leaf_183] at hs
  calc w0 183 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (183 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (183 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_183

theorem w2_leaf_183 : w2 183 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_445 (F := M)
  rw [hpos_leaf_183] at hs
  calc w2 183 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (183 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (183 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_183

theorem hpos_leaf_184 : order.symm (460 : Fin 1024) = (184 : Fin 1024) := by decide
#print axioms hpos_leaf_184

theorem w0_leaf_184 : w0 184 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_460 (F := M)
  rw [hpos_leaf_184] at hs
  calc w0 184 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (184 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (184 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_184

theorem w2_leaf_184 : w2 184 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_460 (F := M)
  rw [hpos_leaf_184] at hs
  calc w2 184 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (184 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (184 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_184

theorem hpos_leaf_185 : order.symm (461 : Fin 1024) = (185 : Fin 1024) := by decide
#print axioms hpos_leaf_185

theorem w0_leaf_185 : w0 185 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_461 (F := M)
  rw [hpos_leaf_185] at hs
  calc w0 185 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (185 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (185 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_185

theorem w2_leaf_185 : w2 185 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_461 (F := M)
  rw [hpos_leaf_185] at hs
  calc w2 185 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (185 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (185 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_185

theorem hpos_leaf_186 : order.symm (476 : Fin 1024) = (186 : Fin 1024) := by decide
#print axioms hpos_leaf_186

theorem w0_leaf_186 : w0 186 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_476 (F := M)
  rw [hpos_leaf_186] at hs
  calc w0 186 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (186 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (186 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_186

theorem w2_leaf_186 : w2 186 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_476 (F := M)
  rw [hpos_leaf_186] at hs
  calc w2 186 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (186 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (186 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_186

theorem hpos_leaf_187 : order.symm (477 : Fin 1024) = (187 : Fin 1024) := by decide
#print axioms hpos_leaf_187

theorem w0_leaf_187 : w0 187 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_477 (F := M)
  rw [hpos_leaf_187] at hs
  calc w0 187 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (187 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (187 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_187

theorem w2_leaf_187 : w2 187 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_477 (F := M)
  rw [hpos_leaf_187] at hs
  calc w2 187 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (187 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (187 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_187

theorem hpos_leaf_188 : order.symm (492 : Fin 1024) = (188 : Fin 1024) := by decide
#print axioms hpos_leaf_188

theorem w0_leaf_188 : w0 188 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_492 (F := M)
  rw [hpos_leaf_188] at hs
  calc w0 188 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (188 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (188 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_188

theorem w2_leaf_188 : w2 188 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_492 (F := M)
  rw [hpos_leaf_188] at hs
  calc w2 188 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (188 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (188 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_188

theorem hpos_leaf_189 : order.symm (493 : Fin 1024) = (189 : Fin 1024) := by decide
#print axioms hpos_leaf_189

theorem w0_leaf_189 : w0 189 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_493 (F := M)
  rw [hpos_leaf_189] at hs
  calc w0 189 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (189 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (189 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_189

theorem w2_leaf_189 : w2 189 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_493 (F := M)
  rw [hpos_leaf_189] at hs
  calc w2 189 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (189 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (189 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_189

theorem hpos_leaf_190 : order.symm (508 : Fin 1024) = (190 : Fin 1024) := by decide
#print axioms hpos_leaf_190

theorem w0_leaf_190 : w0 190 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_508 (F := M)
  rw [hpos_leaf_190] at hs
  calc w0 190 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (190 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (190 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_190

theorem w2_leaf_190 : w2 190 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_508 (F := M)
  rw [hpos_leaf_190] at hs
  calc w2 190 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (190 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (190 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_190

theorem hpos_leaf_191 : order.symm (509 : Fin 1024) = (191 : Fin 1024) := by decide
#print axioms hpos_leaf_191

theorem w0_leaf_191 : w0 191 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_509 (F := M)
  rw [hpos_leaf_191] at hs
  calc w0 191 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (191 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (191 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_191

theorem w2_leaf_191 : w2 191 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_509 (F := M)
  rw [hpos_leaf_191] at hs
  calc w2 191 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (191 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (191 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_191

theorem hpos_leaf_192 : order.symm (524 : Fin 1024) = (192 : Fin 1024) := by decide
#print axioms hpos_leaf_192

theorem w0_leaf_192 : w0 192 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_524 (F := M)
  rw [hpos_leaf_192] at hs
  calc w0 192 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (192 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (192 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_192

theorem w2_leaf_192 : w2 192 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_524 (F := M)
  rw [hpos_leaf_192] at hs
  calc w2 192 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (192 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (192 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_192

theorem hpos_leaf_193 : order.symm (525 : Fin 1024) = (193 : Fin 1024) := by decide
#print axioms hpos_leaf_193

theorem w0_leaf_193 : w0 193 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_525 (F := M)
  rw [hpos_leaf_193] at hs
  calc w0 193 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (193 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (193 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_193

theorem w2_leaf_193 : w2 193 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_525 (F := M)
  rw [hpos_leaf_193] at hs
  calc w2 193 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (193 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (193 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_193

theorem hpos_leaf_194 : order.symm (540 : Fin 1024) = (194 : Fin 1024) := by decide
#print axioms hpos_leaf_194

theorem w0_leaf_194 : w0 194 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_540 (F := M)
  rw [hpos_leaf_194] at hs
  calc w0 194 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (194 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (194 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_194

theorem w2_leaf_194 : w2 194 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_540 (F := M)
  rw [hpos_leaf_194] at hs
  calc w2 194 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (194 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (194 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_194

theorem hpos_leaf_195 : order.symm (541 : Fin 1024) = (195 : Fin 1024) := by decide
#print axioms hpos_leaf_195

theorem w0_leaf_195 : w0 195 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_541 (F := M)
  rw [hpos_leaf_195] at hs
  calc w0 195 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (195 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (195 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_195

theorem w2_leaf_195 : w2 195 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_541 (F := M)
  rw [hpos_leaf_195] at hs
  calc w2 195 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (195 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (195 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_195

theorem hpos_leaf_196 : order.symm (556 : Fin 1024) = (196 : Fin 1024) := by decide
#print axioms hpos_leaf_196

theorem w0_leaf_196 : w0 196 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_556 (F := M)
  rw [hpos_leaf_196] at hs
  calc w0 196 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (196 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (196 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_196

theorem w2_leaf_196 : w2 196 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_556 (F := M)
  rw [hpos_leaf_196] at hs
  calc w2 196 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (196 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (196 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_196

theorem hpos_leaf_197 : order.symm (557 : Fin 1024) = (197 : Fin 1024) := by decide
#print axioms hpos_leaf_197

theorem w0_leaf_197 : w0 197 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_557 (F := M)
  rw [hpos_leaf_197] at hs
  calc w0 197 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (197 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (197 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_197

theorem w2_leaf_197 : w2 197 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_557 (F := M)
  rw [hpos_leaf_197] at hs
  calc w2 197 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (197 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (197 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_197

theorem hpos_leaf_198 : order.symm (572 : Fin 1024) = (198 : Fin 1024) := by decide
#print axioms hpos_leaf_198

theorem w0_leaf_198 : w0 198 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_572 (F := M)
  rw [hpos_leaf_198] at hs
  calc w0 198 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (198 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (198 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_198

theorem w2_leaf_198 : w2 198 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_572 (F := M)
  rw [hpos_leaf_198] at hs
  calc w2 198 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (198 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (198 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_198

theorem hpos_leaf_199 : order.symm (573 : Fin 1024) = (199 : Fin 1024) := by decide
#print axioms hpos_leaf_199

theorem w0_leaf_199 : w0 199 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p0_transport_zero_original_573 (F := M)
  rw [hpos_leaf_199] at hs
  calc w0 199 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (199 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (199 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_199

theorem w2_leaf_199 : w2 199 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk04.p2_transport_zero_original_573 (F := M)
  rw [hpos_leaf_199] at hs
  calc w2 199 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (199 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (199 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_199

theorem hpos_leaf_200 : order.symm (588 : Fin 1024) = (200 : Fin 1024) := by decide
#print axioms hpos_leaf_200

theorem w0_leaf_200 : w0 200 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_588 (F := M)
  rw [hpos_leaf_200] at hs
  calc w0 200 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (200 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (200 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_200

theorem w2_leaf_200 : w2 200 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_588 (F := M)
  rw [hpos_leaf_200] at hs
  calc w2 200 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (200 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (200 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_200

theorem hpos_leaf_201 : order.symm (589 : Fin 1024) = (201 : Fin 1024) := by decide
#print axioms hpos_leaf_201

theorem w0_leaf_201 : w0 201 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_589 (F := M)
  rw [hpos_leaf_201] at hs
  calc w0 201 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (201 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (201 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_201

theorem w2_leaf_201 : w2 201 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_589 (F := M)
  rw [hpos_leaf_201] at hs
  calc w2 201 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (201 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (201 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_201

theorem hpos_leaf_202 : order.symm (604 : Fin 1024) = (202 : Fin 1024) := by decide
#print axioms hpos_leaf_202

theorem w0_leaf_202 : w0 202 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_604 (F := M)
  rw [hpos_leaf_202] at hs
  calc w0 202 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (202 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (202 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_202

theorem w2_leaf_202 : w2 202 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_604 (F := M)
  rw [hpos_leaf_202] at hs
  calc w2 202 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (202 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (202 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_202

theorem hpos_leaf_203 : order.symm (605 : Fin 1024) = (203 : Fin 1024) := by decide
#print axioms hpos_leaf_203

theorem w0_leaf_203 : w0 203 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_605 (F := M)
  rw [hpos_leaf_203] at hs
  calc w0 203 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (203 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (203 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_203

theorem w2_leaf_203 : w2 203 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_605 (F := M)
  rw [hpos_leaf_203] at hs
  calc w2 203 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (203 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (203 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_203

theorem hpos_leaf_204 : order.symm (620 : Fin 1024) = (204 : Fin 1024) := by decide
#print axioms hpos_leaf_204

theorem w0_leaf_204 : w0 204 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_620 (F := M)
  rw [hpos_leaf_204] at hs
  calc w0 204 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (204 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (204 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_204

theorem w2_leaf_204 : w2 204 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_620 (F := M)
  rw [hpos_leaf_204] at hs
  calc w2 204 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (204 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (204 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_204

theorem hpos_leaf_205 : order.symm (621 : Fin 1024) = (205 : Fin 1024) := by decide
#print axioms hpos_leaf_205

theorem w0_leaf_205 : w0 205 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p0_transport_zero_original_621 (F := M)
  rw [hpos_leaf_205] at hs
  calc w0 205 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (205 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (205 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_205

theorem w2_leaf_205 : w2 205 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk05.p2_transport_zero_original_621 (F := M)
  rw [hpos_leaf_205] at hs
  calc w2 205 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (205 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (205 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_205

theorem hpos_leaf_206 : order.symm (636 : Fin 1024) = (206 : Fin 1024) := by decide
#print axioms hpos_leaf_206

theorem w0_leaf_206 : w0 206 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p0_transport_zero_original_636 (F := M)
  rw [hpos_leaf_206] at hs
  calc w0 206 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (206 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (206 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_206

theorem w2_leaf_206 : w2 206 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk18.p2_transport_zero_original_636 (F := M)
  rw [hpos_leaf_206] at hs
  calc w2 206 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (206 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (206 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_206

end
end AspisV8R19.R780Point02WeightSharedChunk03
