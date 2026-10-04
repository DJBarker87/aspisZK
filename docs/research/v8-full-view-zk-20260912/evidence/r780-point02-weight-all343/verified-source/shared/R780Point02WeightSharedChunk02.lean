import AspisV8R19.R780Point02WeightShared
import AspisV8R19.R772Point02DualLeavesChunk02
import AspisV8R19.R772Point02DualLeavesChunk03
import AspisV8R19.R772Point02DualLeavesChunk16
import AspisV8R19.R772Point02DualLeavesChunk17

namespace AspisV8R19.R780Point02WeightSharedChunk02
open AspisV8R16 AspisV8R17 AspisR19
open AspisR19.TwoSwapSourceTable
open AspisV8R19.R780Point02WeightShared
open AspisV8R19.R780Point02WeightPrototype
noncomputable section
set_option autoImplicit false

theorem hpos_leaf_143 : order.symm (125 : Fin 1024) = (143 : Fin 1024) := by decide
#print axioms hpos_leaf_143

theorem w0_leaf_143 : w0 143 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p0_transport_zero_original_125 (F := M)
  rw [hpos_leaf_143] at hs
  calc w0 143 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (143 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (143 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_143

theorem w2_leaf_143 : w2 143 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk02.p2_transport_zero_original_125 (F := M)
  rw [hpos_leaf_143] at hs
  calc w2 143 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (143 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (143 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_143

theorem hpos_leaf_144 : order.symm (140 : Fin 1024) = (144 : Fin 1024) := by decide
#print axioms hpos_leaf_144

theorem w0_leaf_144 : w0 144 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_140 (F := M)
  rw [hpos_leaf_144] at hs
  calc w0 144 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (144 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (144 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_144

theorem w2_leaf_144 : w2 144 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_140 (F := M)
  rw [hpos_leaf_144] at hs
  calc w2 144 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (144 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (144 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_144

theorem hpos_leaf_145 : order.symm (141 : Fin 1024) = (145 : Fin 1024) := by decide
#print axioms hpos_leaf_145

theorem w0_leaf_145 : w0 145 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_141 (F := M)
  rw [hpos_leaf_145] at hs
  calc w0 145 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (145 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (145 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_145

theorem w2_leaf_145 : w2 145 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_141 (F := M)
  rw [hpos_leaf_145] at hs
  calc w2 145 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (145 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (145 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_145

theorem hpos_leaf_146 : order.symm (156 : Fin 1024) = (146 : Fin 1024) := by decide
#print axioms hpos_leaf_146

theorem w0_leaf_146 : w0 146 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_156 (F := M)
  rw [hpos_leaf_146] at hs
  calc w0 146 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (146 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (146 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_146

theorem w2_leaf_146 : w2 146 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_156 (F := M)
  rw [hpos_leaf_146] at hs
  calc w2 146 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (146 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (146 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_146

theorem hpos_leaf_147 : order.symm (157 : Fin 1024) = (147 : Fin 1024) := by decide
#print axioms hpos_leaf_147

theorem w0_leaf_147 : w0 147 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_157 (F := M)
  rw [hpos_leaf_147] at hs
  calc w0 147 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (147 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (147 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_147

theorem w2_leaf_147 : w2 147 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_157 (F := M)
  rw [hpos_leaf_147] at hs
  calc w2 147 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (147 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (147 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_147

theorem hpos_leaf_148 : order.symm (172 : Fin 1024) = (148 : Fin 1024) := by decide
#print axioms hpos_leaf_148

theorem w0_leaf_148 : w0 148 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_172 (F := M)
  rw [hpos_leaf_148] at hs
  calc w0 148 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (148 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (148 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_148

theorem w2_leaf_148 : w2 148 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_172 (F := M)
  rw [hpos_leaf_148] at hs
  calc w2 148 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (148 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (148 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_148

theorem hpos_leaf_149 : order.symm (173 : Fin 1024) = (149 : Fin 1024) := by decide
#print axioms hpos_leaf_149

theorem w0_leaf_149 : w0 149 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_173 (F := M)
  rw [hpos_leaf_149] at hs
  calc w0 149 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (149 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (149 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_149

theorem w2_leaf_149 : w2 149 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_173 (F := M)
  rw [hpos_leaf_149] at hs
  calc w2 149 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (149 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (149 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_149

theorem hpos_leaf_150 : order.symm (188 : Fin 1024) = (150 : Fin 1024) := by decide
#print axioms hpos_leaf_150

theorem w0_leaf_150 : w0 150 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_188 (F := M)
  rw [hpos_leaf_150] at hs
  calc w0 150 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (150 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (150 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_150

theorem w2_leaf_150 : w2 150 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_188 (F := M)
  rw [hpos_leaf_150] at hs
  calc w2 150 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (150 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (150 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_150

theorem hpos_leaf_151 : order.symm (189 : Fin 1024) = (151 : Fin 1024) := by decide
#print axioms hpos_leaf_151

theorem w0_leaf_151 : w0 151 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_189 (F := M)
  rw [hpos_leaf_151] at hs
  calc w0 151 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (151 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (151 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_151

theorem w2_leaf_151 : w2 151 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_189 (F := M)
  rw [hpos_leaf_151] at hs
  calc w2 151 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (151 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (151 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_151

theorem hpos_leaf_152 : order.symm (204 : Fin 1024) = (152 : Fin 1024) := by decide
#print axioms hpos_leaf_152

theorem w0_leaf_152 : w0 152 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_204 (F := M)
  rw [hpos_leaf_152] at hs
  calc w0 152 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (152 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (152 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_152

theorem w2_leaf_152 : w2 152 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_204 (F := M)
  rw [hpos_leaf_152] at hs
  calc w2 152 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (152 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (152 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_152

theorem hpos_leaf_153 : order.symm (205 : Fin 1024) = (153 : Fin 1024) := by decide
#print axioms hpos_leaf_153

theorem w0_leaf_153 : w0 153 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_205 (F := M)
  rw [hpos_leaf_153] at hs
  calc w0 153 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (153 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (153 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_153

theorem w2_leaf_153 : w2 153 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_205 (F := M)
  rw [hpos_leaf_153] at hs
  calc w2 153 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (153 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (153 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_153

theorem hpos_leaf_154 : order.symm (220 : Fin 1024) = (154 : Fin 1024) := by decide
#print axioms hpos_leaf_154

theorem w0_leaf_154 : w0 154 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_220 (F := M)
  rw [hpos_leaf_154] at hs
  calc w0 154 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (154 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (154 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_154

theorem w2_leaf_154 : w2 154 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_220 (F := M)
  rw [hpos_leaf_154] at hs
  calc w2 154 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (154 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (154 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_154

theorem hpos_leaf_155 : order.symm (221 : Fin 1024) = (155 : Fin 1024) := by decide
#print axioms hpos_leaf_155

theorem w0_leaf_155 : w0 155 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_221 (F := M)
  rw [hpos_leaf_155] at hs
  calc w0 155 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (155 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (155 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_155

theorem w2_leaf_155 : w2 155 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_221 (F := M)
  rw [hpos_leaf_155] at hs
  calc w2 155 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (155 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (155 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_155

theorem hpos_leaf_156 : order.symm (236 : Fin 1024) = (156 : Fin 1024) := by decide
#print axioms hpos_leaf_156

theorem w0_leaf_156 : w0 156 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_236 (F := M)
  rw [hpos_leaf_156] at hs
  calc w0 156 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (156 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (156 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_156

theorem w2_leaf_156 : w2 156 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_236 (F := M)
  rw [hpos_leaf_156] at hs
  calc w2 156 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (156 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (156 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_156

theorem hpos_leaf_157 : order.symm (237 : Fin 1024) = (157 : Fin 1024) := by decide
#print axioms hpos_leaf_157

theorem w0_leaf_157 : w0 157 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_237 (F := M)
  rw [hpos_leaf_157] at hs
  calc w0 157 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (157 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (157 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_157

theorem w2_leaf_157 : w2 157 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_237 (F := M)
  rw [hpos_leaf_157] at hs
  calc w2 157 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (157 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (157 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_157

theorem hpos_leaf_158 : order.symm (252 : Fin 1024) = (158 : Fin 1024) := by decide
#print axioms hpos_leaf_158

theorem w0_leaf_158 : w0 158 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_252 (F := M)
  rw [hpos_leaf_158] at hs
  calc w0 158 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (158 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (158 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_158

theorem w2_leaf_158 : w2 158 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_252 (F := M)
  rw [hpos_leaf_158] at hs
  calc w2 158 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (158 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (158 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_158

theorem hpos_leaf_159 : order.symm (253 : Fin 1024) = (159 : Fin 1024) := by decide
#print axioms hpos_leaf_159

theorem w0_leaf_159 : w0 159 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_253 (F := M)
  rw [hpos_leaf_159] at hs
  calc w0 159 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (159 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (159 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_159

theorem w2_leaf_159 : w2 159 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_253 (F := M)
  rw [hpos_leaf_159] at hs
  calc w2 159 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (159 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (159 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_159

theorem hpos_leaf_160 : order.symm (268 : Fin 1024) = (160 : Fin 1024) := by decide
#print axioms hpos_leaf_160

theorem w0_leaf_160 : w0 160 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p0_transport_zero_original_268 (F := M)
  rw [hpos_leaf_160] at hs
  calc w0 160 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (160 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (160 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_160

theorem w2_leaf_160 : w2 160 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk16.p2_transport_zero_original_268 (F := M)
  rw [hpos_leaf_160] at hs
  calc w2 160 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (160 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (160 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_160

theorem hpos_leaf_161 : order.symm (269 : Fin 1024) = (161 : Fin 1024) := by decide
#print axioms hpos_leaf_161

theorem w0_leaf_161 : w0 161 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_269 (F := M)
  rw [hpos_leaf_161] at hs
  calc w0 161 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (161 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (161 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_161

theorem w2_leaf_161 : w2 161 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_269 (F := M)
  rw [hpos_leaf_161] at hs
  calc w2 161 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (161 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (161 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_161

theorem hpos_leaf_162 : order.symm (284 : Fin 1024) = (162 : Fin 1024) := by decide
#print axioms hpos_leaf_162

theorem w0_leaf_162 : w0 162 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_284 (F := M)
  rw [hpos_leaf_162] at hs
  calc w0 162 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (162 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (162 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_162

theorem w2_leaf_162 : w2 162 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_284 (F := M)
  rw [hpos_leaf_162] at hs
  calc w2 162 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (162 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (162 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_162

theorem hpos_leaf_163 : order.symm (285 : Fin 1024) = (163 : Fin 1024) := by decide
#print axioms hpos_leaf_163

theorem w0_leaf_163 : w0 163 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_285 (F := M)
  rw [hpos_leaf_163] at hs
  calc w0 163 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (163 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (163 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_163

theorem w2_leaf_163 : w2 163 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_285 (F := M)
  rw [hpos_leaf_163] at hs
  calc w2 163 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (163 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (163 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_163

theorem hpos_leaf_164 : order.symm (300 : Fin 1024) = (164 : Fin 1024) := by decide
#print axioms hpos_leaf_164

theorem w0_leaf_164 : w0 164 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_300 (F := M)
  rw [hpos_leaf_164] at hs
  calc w0 164 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (164 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (164 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_164

theorem w2_leaf_164 : w2 164 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_300 (F := M)
  rw [hpos_leaf_164] at hs
  calc w2 164 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (164 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (164 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_164

theorem hpos_leaf_165 : order.symm (301 : Fin 1024) = (165 : Fin 1024) := by decide
#print axioms hpos_leaf_165

theorem w0_leaf_165 : w0 165 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_301 (F := M)
  rw [hpos_leaf_165] at hs
  calc w0 165 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (165 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (165 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_165

theorem w2_leaf_165 : w2 165 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_301 (F := M)
  rw [hpos_leaf_165] at hs
  calc w2 165 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (165 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (165 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_165

theorem hpos_leaf_166 : order.symm (316 : Fin 1024) = (166 : Fin 1024) := by decide
#print axioms hpos_leaf_166

theorem w0_leaf_166 : w0 166 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_316 (F := M)
  rw [hpos_leaf_166] at hs
  calc w0 166 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (166 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (166 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_166

theorem w2_leaf_166 : w2 166 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_316 (F := M)
  rw [hpos_leaf_166] at hs
  calc w2 166 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (166 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (166 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_166

theorem hpos_leaf_167 : order.symm (317 : Fin 1024) = (167 : Fin 1024) := by decide
#print axioms hpos_leaf_167

theorem w0_leaf_167 : w0 167 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_317 (F := M)
  rw [hpos_leaf_167] at hs
  calc w0 167 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (167 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (167 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_167

theorem w2_leaf_167 : w2 167 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_317 (F := M)
  rw [hpos_leaf_167] at hs
  calc w2 167 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (167 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (167 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_167

theorem hpos_leaf_168 : order.symm (332 : Fin 1024) = (168 : Fin 1024) := by decide
#print axioms hpos_leaf_168

theorem w0_leaf_168 : w0 168 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_332 (F := M)
  rw [hpos_leaf_168] at hs
  calc w0 168 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (168 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (168 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_168

theorem w2_leaf_168 : w2 168 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_332 (F := M)
  rw [hpos_leaf_168] at hs
  calc w2 168 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (168 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (168 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_168

theorem hpos_leaf_169 : order.symm (333 : Fin 1024) = (169 : Fin 1024) := by decide
#print axioms hpos_leaf_169

theorem w0_leaf_169 : w0 169 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_333 (F := M)
  rw [hpos_leaf_169] at hs
  calc w0 169 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (169 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (169 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_169

theorem w2_leaf_169 : w2 169 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_333 (F := M)
  rw [hpos_leaf_169] at hs
  calc w2 169 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (169 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (169 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_169

theorem hpos_leaf_170 : order.symm (348 : Fin 1024) = (170 : Fin 1024) := by decide
#print axioms hpos_leaf_170

theorem w0_leaf_170 : w0 170 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_348 (F := M)
  rw [hpos_leaf_170] at hs
  calc w0 170 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (170 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (170 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_170

theorem w2_leaf_170 : w2 170 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_348 (F := M)
  rw [hpos_leaf_170] at hs
  calc w2 170 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (170 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (170 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_170

theorem hpos_leaf_171 : order.symm (349 : Fin 1024) = (171 : Fin 1024) := by decide
#print axioms hpos_leaf_171

theorem w0_leaf_171 : w0 171 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_349 (F := M)
  rw [hpos_leaf_171] at hs
  calc w0 171 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (171 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (171 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_171

theorem w2_leaf_171 : w2 171 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_349 (F := M)
  rw [hpos_leaf_171] at hs
  calc w2 171 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (171 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (171 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_171

theorem hpos_leaf_172 : order.symm (364 : Fin 1024) = (172 : Fin 1024) := by decide
#print axioms hpos_leaf_172

theorem w0_leaf_172 : w0 172 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_364 (F := M)
  rw [hpos_leaf_172] at hs
  calc w0 172 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (172 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (172 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_172

theorem w2_leaf_172 : w2 172 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_364 (F := M)
  rw [hpos_leaf_172] at hs
  calc w2 172 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (172 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (172 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_172

theorem hpos_leaf_173 : order.symm (365 : Fin 1024) = (173 : Fin 1024) := by decide
#print axioms hpos_leaf_173

theorem w0_leaf_173 : w0 173 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p0_transport_zero_original_365 (F := M)
  rw [hpos_leaf_173] at hs
  calc w0 173 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (173 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (173 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_173

theorem w2_leaf_173 : w2 173 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk03.p2_transport_zero_original_365 (F := M)
  rw [hpos_leaf_173] at hs
  calc w2 173 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (173 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (173 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_173

theorem hpos_leaf_174 : order.symm (380 : Fin 1024) = (174 : Fin 1024) := by decide
#print axioms hpos_leaf_174

theorem w0_leaf_174 : w0 174 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p0_transport_zero_original_380 (F := M)
  rw [hpos_leaf_174] at hs
  calc w0 174 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point0 j.val) (174 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w0_at (i := (174 : Fin 1024))
       _ = 0 := hs

#print axioms w0_leaf_174

theorem w2_leaf_174 : w2 174 = 0 := by
  have hs := AspisV8R19.R772Point02DualLeavesChunk17.p2_transport_zero_original_380 (F := M)
  rw [hpos_leaf_174] at hs
  calc w2 174 = AspisV8R16.transportDual inactive (1023 : Fin 1024) order (fun j : Fin 1024 => sourcePointBasis point2 j.val) (174 : Fin 1024) := by
          simpa using AspisV8R19.R780Point02WeightShared.w2_at (i := (174 : Fin 1024))
       _ = 0 := hs

#print axioms w2_leaf_174

end
end AspisV8R19.R780Point02WeightSharedChunk02
