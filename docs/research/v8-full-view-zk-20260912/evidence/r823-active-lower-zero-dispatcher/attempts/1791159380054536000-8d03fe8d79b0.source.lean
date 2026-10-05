import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R801LiteralActiveEntries
import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R766BlockOrderEquivalences
import AspisV8R19.R811SourceLowerZeroPrototype
import AspisV8R19.R811SourceLowerZeroChunk01
import AspisV8R19.R811SourceLowerZeroChunk02
import AspisV8R19.R811SourceLowerZeroChunk03
import AspisV8R19.R811SourceLowerZeroChunk04
import AspisV8R19.R811SourceLowerZeroChunk05
import AspisV8R19.R811SourceLowerZeroChunk06
import AspisV8R19.R811SourceLowerZeroChunk07
import AspisV8R19.R811SourceLowerZeroChunk08
import AspisV8R19.R811SourceLowerZeroChunk09
import AspisV8R19.R811SourceLowerZeroChunk10
import AspisV8R19.R811SourceLowerZeroChunk11
import AspisV8R19.R811SourceLowerZeroChunk12
import AspisV8R19.R811SourceLowerZeroChunk13
import AspisV8R19.R811SourceLowerZeroChunk14
import AspisV8R19.R811SourceLowerZeroChunk15
import AspisV8R19.R811SourceLowerZeroChunk16
import AspisV8R19.R811SourceLowerZeroChunk17
import AspisV8R19.R811SourceLowerZeroChunk18
import AspisV8R19.R811SourceLowerZeroChunk19
import AspisV8R19.R811SourceLowerZeroChunk20
import AspisV8R19.R811SourceLowerZeroChunk21
import AspisV8R19.R811SourceLowerZeroChunk22
import AspisV8R19.R811SourceLowerZeroChunk23
import AspisV8R19.R811SourceLowerZeroChunk24
import AspisV8R19.R811SourceLowerZeroChunk25
import AspisV8R19.R811SourceLowerZeroChunk26
import AspisV8R19.R811SourceLowerZeroChunk27
import AspisV8R19.R811SourceLowerZeroChunk28
import AspisV8R19.R811SourceLowerZeroChunk29
import AspisV8R19.R811SourceLowerZeroChunk30
import AspisV8R19.R811SourceLowerZeroChunk31
import AspisV8R19.R811SourceLowerZeroChunk32
import AspisV8R19.R811SourceLowerZeroChunk33
import AspisV8R19.R811SourceLowerZeroChunk34
import AspisV8R19.R811SourceLowerZeroChunk35
import AspisV8R19.R811SourceLowerZeroChunk36
import AspisV8R19.R811SourceLowerZeroChunk37
import AspisV8R19.R811SourceLowerZeroChunk38
import AspisV8R19.R811SourceLowerZeroChunk39
import AspisV8R19.R811SourceLowerZeroChunk40
import AspisV8R19.R811SourceLowerZeroChunk41
import AspisV8R19.R811SourceLowerZeroChunk42
import AspisV8R19.R811SourceLowerZeroChunk43
import AspisV8R19.R811SourceLowerZeroChunk44
import AspisV8R19.R811SourceLowerZeroChunk45
import AspisV8R19.R811SourceLowerZeroChunk46
import AspisV8R19.R811SourceLowerZeroChunk47
import AspisV8R19.R811SourceLowerZeroChunk48
import AspisV8R19.R811SourceLowerZeroChunk49
import AspisV8R19.R811SourceLowerZeroChunk50
import AspisV8R19.R811SourceLowerZeroChunk51
import AspisV8R19.R811SourceLowerZeroChunk52
import AspisV8R19.R811SourceLowerZeroChunk53
import AspisV8R19.R811SourceLowerZeroChunk54

set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R823ActiveLowerZeroDispatcher
open AspisV8R19.R807SourceBlock01Binding
open AspisV8R19.R801LiteralActiveEntries
open AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R806LiteralBlockLayout
open AspisV8R19.R766BlockOrderEquivalences
noncomputable section

theorem active_row_lower_zero_1 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨1, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨1, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨36, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨1, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat36_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨1, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_1

theorem active_row_lower_zero_2 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨2, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨2, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨37, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨2, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat37_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨2, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_2

theorem active_row_lower_zero_3 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨3, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨3, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨38, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨3, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat38_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨3, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_3

theorem active_row_lower_zero_4 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨4, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨4, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨39, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨4, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat39_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨4, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_4

theorem active_row_lower_zero_5 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨5, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨5, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨40, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨5, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat40_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨5, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_5

theorem active_row_lower_zero_6 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨6, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨6, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨41, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨6, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat41_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨6, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_6

theorem active_row_lower_zero_7 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨7, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨7, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨18, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨7, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat18_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨7, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_7

theorem active_row_lower_zero_8 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨8, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨8, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨19, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨8, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat19_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨8, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_8

theorem active_row_lower_zero_9 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨9, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨9, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨20, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨9, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat20_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨9, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_9

theorem active_row_lower_zero_10 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨10, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨10, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨21, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨10, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat21_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨10, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_10

theorem active_row_lower_zero_11 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨11, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨11, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨22, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨11, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat22_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨11, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_11

theorem active_row_lower_zero_12 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨12, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨12, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨23, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨12, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat23_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨12, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_12

theorem active_row_lower_zero_13 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨13, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨13, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨24, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨13, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat24_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨13, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_13

theorem active_row_lower_zero_14 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨14, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨14, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨25, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨14, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat25_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨14, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_14

theorem active_row_lower_zero_15 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨15, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨15, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨26, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨15, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat26_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨15, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_15

theorem active_row_lower_zero_16 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨16, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨16, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨27, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨16, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat27_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨16, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_16

theorem active_row_lower_zero_17 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨17, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨17, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨28, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨17, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat28_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨17, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_17

theorem active_row_lower_zero_18 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨18, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨18, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨29, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨18, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat29_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨18, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_18

theorem active_row_lower_zero_19 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨19, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨19, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨30, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨19, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat30_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨19, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_19

theorem active_row_lower_zero_20 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨20, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨20, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨31, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨20, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat31_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨20, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_20

theorem active_row_lower_zero_21 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨21, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨21, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨32, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨21, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat32_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨21, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_21

theorem active_row_lower_zero_22 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨22, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨22, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨33, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨22, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat33_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨22, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_22

theorem active_row_lower_zero_23 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨23, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨23, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨10, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨23, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat10_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨23, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_23

theorem active_row_lower_zero_24 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨24, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨24, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨11, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨24, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat11_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨24, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_24

theorem active_row_lower_zero_25 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨25, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨25, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨12, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨25, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat12_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨25, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_25

theorem active_row_lower_zero_26 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨26, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨26, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨13, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨26, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat13_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨26, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_26

theorem active_row_lower_zero_27 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨27, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨27, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨14, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨27, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat14_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨27, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_27

theorem active_row_lower_zero_28 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨28, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨28, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨15, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨28, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat15_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨28, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_28

theorem active_row_lower_zero_29 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨29, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨29, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨16, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨29, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat16_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨29, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_29

theorem active_row_lower_zero_30 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨30, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨30, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨17, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨30, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat17_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨30, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_30

theorem active_row_lower_zero_31 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨31, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨31, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨7, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨31, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat7_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨31, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_31

theorem active_row_lower_zero_32 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨32, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨32, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨8, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨32, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat8_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨32, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_32

theorem active_row_lower_zero_33 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨33, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨33, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨9, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨33, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat9_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨33, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_33

theorem active_row_lower_zero_34 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨34, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨34, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨6, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨34, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat6_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨34, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_34

theorem active_row_lower_zero_35 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨35, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨35, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨34, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨35, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat34_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨35, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_35

theorem active_row_lower_zero_36 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨36, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨36, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨42, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨36, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat42_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨36, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_36

theorem active_row_lower_zero_37 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨37, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨37, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨43, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨37, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat43_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨37, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_37

theorem active_row_lower_zero_38 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨38, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨38, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨44, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨38, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat44_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨38, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_38

theorem active_row_lower_zero_39 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨39, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨39, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨45, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨39, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat45_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨39, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_39

theorem active_row_lower_zero_40 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨40, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨40, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨46, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨40, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat46_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨40, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_40

theorem active_row_lower_zero_41 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨41, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨41, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨47, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨41, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat47_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨41, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_41

theorem active_row_lower_zero_42 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨42, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨42, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨48, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨42, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat48_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨42, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_42

theorem active_row_lower_zero_43 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨43, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨43, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨49, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨43, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat49_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨43, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_43

theorem active_row_lower_zero_44 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨44, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨44, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨50, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨44, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat50_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨44, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_44

theorem active_row_lower_zero_45 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨45, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨45, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨51, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨45, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat51_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨45, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_45

theorem active_row_lower_zero_46 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨46, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨46, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨52, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨46, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat52_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨46, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_46

theorem active_row_lower_zero_47 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨47, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨47, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨53, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨47, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat53_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨47, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_47

theorem active_row_lower_zero_48 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨48, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨48, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨54, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨48, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat54_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨48, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_48

theorem active_row_lower_zero_49 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨49, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨49, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨55, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨49, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat55_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨49, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_49

theorem active_row_lower_zero_50 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨50, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨50, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨56, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨50, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat56_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨50, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_50

theorem active_row_lower_zero_51 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨51, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨51, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨57, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨51, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat57_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨51, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_51

theorem active_row_lower_zero_52 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨52, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨52, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨58, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨52, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat58_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨52, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_52

theorem active_row_lower_zero_53 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨53, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨53, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨59, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨53, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat59_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨53, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_53

theorem active_row_lower_zero_54 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨54, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨54, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨60, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨54, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat60_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨54, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_54

theorem active_row_lower_zero_55 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨55, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨55, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨61, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨55, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat61_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨55, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_55

theorem active_row_lower_zero_56 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨56, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨56, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨62, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨56, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat62_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨56, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_56

theorem active_row_lower_zero_57 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨57, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨57, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨63, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨57, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat63_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨57, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_57

theorem active_row_lower_zero_58 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨58, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨58, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨64, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨58, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat64_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨58, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_58

theorem active_row_lower_zero_59 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨59, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨59, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨65, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨59, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat65_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨59, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_59

theorem active_row_lower_zero_60 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨60, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨60, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨66, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨60, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat66_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨60, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_60

theorem active_row_lower_zero_61 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨61, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨61, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨67, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨61, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat67_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨61, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_61

theorem active_row_lower_zero_62 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨62, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨62, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨68, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨62, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat68_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨62, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_62

theorem active_row_lower_zero_63 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨63, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨63, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨69, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨63, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat69_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨63, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_63

theorem active_row_lower_zero_64 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨64, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨64, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨70, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨64, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat70_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨64, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_64

theorem active_row_lower_zero_65 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨65, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨65, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨71, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨65, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat71_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨65, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_65

theorem active_row_lower_zero_66 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨66, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨66, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨84, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨66, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat84_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨66, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_66

theorem active_row_lower_zero_67 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨67, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨67, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨85, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨67, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat85_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨67, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_67

theorem active_row_lower_zero_68 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨68, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨68, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨86, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨68, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat86_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨68, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_68

theorem active_row_lower_zero_69 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨69, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨69, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨87, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨69, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat87_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨69, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_69

theorem active_row_lower_zero_70 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨70, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨70, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨88, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨70, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat88_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨70, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_70

theorem active_row_lower_zero_71 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨71, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨71, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨89, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨71, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat89_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨71, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_71

theorem active_row_lower_zero_72 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨72, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨72, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨90, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨72, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat90_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨72, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_72

theorem active_row_lower_zero_73 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨73, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨73, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨91, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨73, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat91_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨73, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_73

theorem active_row_lower_zero_74 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨74, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨74, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨92, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨74, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat92_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨74, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_74

theorem active_row_lower_zero_75 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨75, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨75, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨93, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨75, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat93_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨75, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_75

theorem active_row_lower_zero_76 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨76, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨76, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨94, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨76, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat94_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨76, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_76

theorem active_row_lower_zero_77 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨77, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨77, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨95, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨77, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat95_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨77, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_77

theorem active_row_lower_zero_78 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨78, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨78, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨96, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨78, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat96_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨78, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_78

theorem active_row_lower_zero_79 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨79, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨79, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨97, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨79, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat97_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨79, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_79

theorem active_row_lower_zero_80 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨80, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨80, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨98, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨80, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat98_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨80, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_80

theorem active_row_lower_zero_81 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨81, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨81, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨99, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨81, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat99_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨81, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_81

theorem active_row_lower_zero_82 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨82, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨82, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨76, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨82, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat76_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨82, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_82

theorem active_row_lower_zero_83 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨83, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨83, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨77, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨83, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat77_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨83, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_83

theorem active_row_lower_zero_84 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨84, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨84, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨78, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨84, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat78_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨84, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_84

theorem active_row_lower_zero_85 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨85, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨85, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨79, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨85, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat79_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨85, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_85

theorem active_row_lower_zero_86 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨86, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨86, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨80, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨86, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat80_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨86, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_86

theorem active_row_lower_zero_87 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨87, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨87, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨81, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨87, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat81_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨87, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_87

theorem active_row_lower_zero_88 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨88, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨88, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨82, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨88, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat82_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨88, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_88

theorem active_row_lower_zero_89 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨89, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨89, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨83, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨89, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat83_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨89, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_89

theorem active_row_lower_zero_90 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨90, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨90, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨74, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨90, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat74_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨90, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_90

theorem active_row_lower_zero_91 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨91, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨91, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨75, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨91, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat75_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨91, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_91

theorem active_row_lower_zero_92 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨92, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨92, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨125, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨92, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat125_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨92, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_92

theorem active_row_lower_zero_93 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨93, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨93, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨121, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨93, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat121_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨93, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_93

theorem active_row_lower_zero_94 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨94, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨94, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨122, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨94, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat122_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨94, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_94

theorem active_row_lower_zero_95 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨95, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨95, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨123, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨95, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat123_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨95, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_95

theorem active_row_lower_zero_96 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨96, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨96, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨124, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨96, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat124_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨96, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_96

theorem active_row_lower_zero_97 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨97, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨97, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨105, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨97, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat105_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨97, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_97

theorem active_row_lower_zero_98 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨98, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨98, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨106, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨98, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat106_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨98, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_98

theorem active_row_lower_zero_99 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨99, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨99, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨107, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨99, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat107_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨99, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_99

theorem active_row_lower_zero_100 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨100, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨100, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨108, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨100, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat108_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨100, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_100

theorem active_row_lower_zero_101 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨101, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨101, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨109, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨101, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat109_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨101, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_101

theorem active_row_lower_zero_102 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨102, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨102, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨110, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨102, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat110_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨102, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_102

theorem active_row_lower_zero_103 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨103, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨103, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨111, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨103, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat111_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨103, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_103

theorem active_row_lower_zero_104 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨104, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨104, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨112, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨104, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat112_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨104, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_104

theorem active_row_lower_zero_105 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨105, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨105, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨113, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨105, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat113_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨105, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_105

theorem active_row_lower_zero_106 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨106, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨106, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨114, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨106, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat114_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨106, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_106

theorem active_row_lower_zero_107 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨107, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨107, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨115, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨107, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat115_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨107, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_107

theorem active_row_lower_zero_108 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨108, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨108, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨116, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨108, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat116_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨108, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_108

theorem active_row_lower_zero_109 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨109, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨109, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨117, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨109, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat117_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨109, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_109

theorem active_row_lower_zero_110 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨110, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨110, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨118, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨110, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat118_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨110, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_110

theorem active_row_lower_zero_111 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨111, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨111, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨119, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨111, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat119_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨111, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_111

theorem active_row_lower_zero_112 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨112, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨112, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨120, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨112, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat120_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨112, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_112

theorem active_row_lower_zero_113 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨113, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨113, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨101, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨113, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat101_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨113, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_113

theorem active_row_lower_zero_114 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨114, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨114, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨102, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨114, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat102_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨114, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_114

theorem active_row_lower_zero_115 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨115, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨115, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨103, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨115, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat103_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨115, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_115

theorem active_row_lower_zero_116 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨116, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨116, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨104, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨116, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat104_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨116, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_116

theorem active_row_lower_zero_117 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨117, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨117, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨100, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨117, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat100_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨117, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_117

theorem active_row_lower_zero_118 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨118, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨118, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨133, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨118, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat133_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨118, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_118

theorem active_row_lower_zero_119 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨119, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨119, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨134, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨119, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat134_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨119, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_119

theorem active_row_lower_zero_120 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨120, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨120, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨132, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨120, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat132_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨120, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_120

theorem active_row_lower_zero_121 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨121, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨121, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨130, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨121, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat130_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨121, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_121

theorem active_row_lower_zero_122 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨122, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨122, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨131, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨122, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat131_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨122, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_122

theorem active_row_lower_zero_123 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨123, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨123, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨126, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨123, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat126_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨123, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_123

theorem active_row_lower_zero_124 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨124, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨124, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨127, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨124, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat127_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨124, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_124

theorem active_row_lower_zero_125 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨125, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨125, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨128, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨125, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat128_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨125, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_125

theorem active_row_lower_zero_126 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨126, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨126, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨129, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨126, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat129_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨126, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_126

theorem active_row_lower_zero_127 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨127, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨127, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨141, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨127, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat141_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨127, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_127

theorem active_row_lower_zero_128 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨128, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨128, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨139, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨128, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat139_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨128, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_128

theorem active_row_lower_zero_129 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨129, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨129, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨140, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨129, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat140_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨129, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_129

theorem active_row_lower_zero_130 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨130, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨130, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨135, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨130, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat135_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨130, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_130

theorem active_row_lower_zero_131 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨131, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨131, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨136, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨131, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat136_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨131, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_131

theorem active_row_lower_zero_132 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨132, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨132, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨137, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨132, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat137_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨132, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_132

theorem active_row_lower_zero_133 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨133, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨133, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨138, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨133, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat138_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨133, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_133

theorem active_row_lower_zero_134 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨134, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨134, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨142, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨134, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat142_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨134, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_134

theorem active_row_lower_zero_135 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨135, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨135, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨143, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨135, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat143_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨135, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_135

theorem active_row_lower_zero_136 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨136, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨136, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨144, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨136, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat144_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨136, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_136

theorem active_row_lower_zero_137 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨137, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨137, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨145, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨137, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat145_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨137, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_137

theorem active_row_lower_zero_138 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨138, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨138, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨146, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨138, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat146_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨138, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_138

theorem active_row_lower_zero_139 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨139, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨139, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨147, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨139, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat147_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨139, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_139

theorem active_row_lower_zero_140 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨140, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨140, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨148, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨140, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat148_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨140, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_140

theorem active_row_lower_zero_141 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨141, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨141, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨149, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨141, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat149_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨141, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_141

theorem active_row_lower_zero_142 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨142, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨142, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨156, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨142, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat156_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨142, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_142

theorem active_row_lower_zero_143 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨143, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨143, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨154, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨143, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat154_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨143, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_143

theorem active_row_lower_zero_144 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨144, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨144, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨155, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨144, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat155_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨144, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_144

theorem active_row_lower_zero_145 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨145, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨145, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨152, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨145, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat152_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨145, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_145

theorem active_row_lower_zero_146 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨146, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨146, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨153, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨146, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat153_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨146, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_146

theorem active_row_lower_zero_147 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨147, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨147, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨150, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨147, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat150_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨147, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_147

theorem active_row_lower_zero_148 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨148, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨148, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨151, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨148, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat151_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨148, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_148

theorem active_row_lower_zero_149 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨149, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨149, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨163, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨149, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat163_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨149, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_149

theorem active_row_lower_zero_150 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨150, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨150, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨161, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨150, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat161_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨150, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_150

theorem active_row_lower_zero_151 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨151, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨151, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨162, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨151, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat162_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨151, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_151

theorem active_row_lower_zero_152 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨152, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨152, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨157, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨152, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat157_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨152, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_152

theorem active_row_lower_zero_153 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨153, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨153, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨158, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨153, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat158_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨153, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_153

theorem active_row_lower_zero_154 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨154, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨154, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨159, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨154, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat159_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨154, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_154

theorem active_row_lower_zero_155 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨155, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨155, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨160, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨155, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat160_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨155, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_155

theorem active_row_lower_zero_156 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨156, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨156, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨188, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨156, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat188_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨156, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_156

theorem active_row_lower_zero_157 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨157, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨157, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨189, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨157, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat189_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨157, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_157

theorem active_row_lower_zero_158 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨158, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨158, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨184, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨158, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat184_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨158, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_158

theorem active_row_lower_zero_159 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨159, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨159, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨185, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨159, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat185_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨159, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_159

theorem active_row_lower_zero_160 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨160, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨160, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨186, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨160, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat186_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨160, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_160

theorem active_row_lower_zero_161 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨161, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨161, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨187, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨161, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat187_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨161, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_161

theorem active_row_lower_zero_162 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨162, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨162, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨176, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨162, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat176_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨162, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_162

theorem active_row_lower_zero_163 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨163, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨163, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨177, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨163, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat177_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨163, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_163

theorem active_row_lower_zero_164 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨164, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨164, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨178, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨164, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat178_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨164, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_164

theorem active_row_lower_zero_165 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨165, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨165, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨179, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨165, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat179_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨165, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_165

theorem active_row_lower_zero_166 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨166, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨166, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨180, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨166, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat180_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨166, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_166

theorem active_row_lower_zero_167 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨167, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨167, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨181, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨167, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat181_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨167, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_167

theorem active_row_lower_zero_168 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨168, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨168, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨182, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨168, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat182_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨168, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_168

theorem active_row_lower_zero_169 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨169, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨169, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨183, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨169, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat183_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨169, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_169

theorem active_row_lower_zero_170 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨170, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨170, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨168, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨170, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat168_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨170, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_170

theorem active_row_lower_zero_171 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨171, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨171, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨169, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨171, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat169_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨171, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_171

theorem active_row_lower_zero_172 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨172, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨172, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨170, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨172, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat170_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨172, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_172

theorem active_row_lower_zero_173 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨173, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨173, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨171, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨173, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat171_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨173, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_173

theorem active_row_lower_zero_174 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨174, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨174, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨172, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨174, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat172_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨174, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_174

theorem active_row_lower_zero_175 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨175, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨175, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨173, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨175, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat173_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨175, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_175

theorem active_row_lower_zero_176 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨176, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨176, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨174, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨176, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat174_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨176, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_176

theorem active_row_lower_zero_177 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨177, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨177, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨175, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨177, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat175_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨177, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_177

theorem active_row_lower_zero_178 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨178, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨178, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨166, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨178, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat166_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨178, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_178

theorem active_row_lower_zero_179 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨179, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨179, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨167, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨179, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat167_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨179, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_179

theorem active_row_lower_zero_180 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨180, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨180, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨164, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨180, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat164_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨180, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_180

theorem active_row_lower_zero_181 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨181, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨181, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨165, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨181, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat165_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨181, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_181

theorem active_row_lower_zero_182 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨182, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨182, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨221, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨182, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat221_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨182, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_182

theorem active_row_lower_zero_183 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨183, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨183, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨205, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨183, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat205_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨183, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_183

theorem active_row_lower_zero_184 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨184, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨184, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨206, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨184, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat206_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨184, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_184

theorem active_row_lower_zero_185 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨185, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨185, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨207, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨185, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat207_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨185, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_185

theorem active_row_lower_zero_186 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨186, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨186, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨208, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨186, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat208_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨186, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_186

theorem active_row_lower_zero_187 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨187, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨187, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨209, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨187, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat209_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨187, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_187

theorem active_row_lower_zero_188 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨188, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨188, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨210, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨188, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat210_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨188, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_188

theorem active_row_lower_zero_189 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨189, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨189, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨211, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨189, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat211_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨189, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_189

theorem active_row_lower_zero_190 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨190, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨190, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨212, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨190, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat212_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨190, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_190

theorem active_row_lower_zero_191 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨191, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨191, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨213, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨191, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat213_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨191, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_191

theorem active_row_lower_zero_192 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨192, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨192, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨214, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨192, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat214_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨192, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_192

theorem active_row_lower_zero_193 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨193, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨193, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨215, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨193, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat215_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨193, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_193

theorem active_row_lower_zero_194 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨194, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨194, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨216, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨194, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat216_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨194, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_194

theorem active_row_lower_zero_195 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨195, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨195, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨217, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨195, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat217_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨195, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_195

theorem active_row_lower_zero_196 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨196, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨196, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨218, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨196, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat218_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨196, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_196

theorem active_row_lower_zero_197 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨197, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨197, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨219, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨197, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat219_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨197, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_197

theorem active_row_lower_zero_198 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨198, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨198, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨220, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨198, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat220_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨198, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_198

theorem active_row_lower_zero_199 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨199, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨199, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨197, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨199, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat197_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨199, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_199

theorem active_row_lower_zero_200 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨200, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨200, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨198, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨200, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat198_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨200, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_200

theorem active_row_lower_zero_201 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨201, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨201, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨199, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨201, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat199_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨201, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_201

theorem active_row_lower_zero_202 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨202, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨202, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨200, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨202, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat200_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨202, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_202

theorem active_row_lower_zero_203 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨203, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨203, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨201, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨203, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat201_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨203, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_203

theorem active_row_lower_zero_204 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨204, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨204, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨202, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨204, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat202_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨204, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_204

theorem active_row_lower_zero_205 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨205, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨205, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨203, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨205, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat203_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨205, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_205

theorem active_row_lower_zero_206 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨206, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨206, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨204, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨206, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat204_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨206, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_206

theorem active_row_lower_zero_207 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨207, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨207, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨193, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨207, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat193_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨207, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_207

theorem active_row_lower_zero_208 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨208, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨208, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨194, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨208, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat194_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨208, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_208

theorem active_row_lower_zero_209 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨209, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨209, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨195, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨209, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat195_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨209, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_209

theorem active_row_lower_zero_210 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨210, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨210, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨196, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨210, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat196_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨210, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_210

theorem active_row_lower_zero_211 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨211, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨211, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨190, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨211, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat190_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨211, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_211

theorem active_row_lower_zero_212 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨212, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨212, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨191, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨212, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat191_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨212, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_212

theorem active_row_lower_zero_213 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨213, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨213, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨192, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨213, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk54.rowFlat192_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨213, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_213

theorem active_row_lower_zero_0 (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition (⟨0, by decide⟩ : Fin 214)))):
    fixedSourceMatrix (activePosition (⟨0, by decide⟩ : Fin 214)) (colOrder j) = 0 := by
  let flat : Fin 222 := ⟨35, by decide⟩
  have hflat : rowOrderInv (activePosition (⟨0, by decide⟩ : Fin 214)) = flat := by decide
  have hineq : blockLabel j < blockLabel flat := by
    rw [← hflat]
    exact h
  have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroPrototype.rowFlat35_lower_zero j hineq
  change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
  have hrow : rowOrder flat = activePosition (⟨0, by decide⟩ : Fin 214) := by
    rw [← hflat]
    exact row_right _
  rw [hrow] at hr
  simpa [activePosition] using hr
#print axioms active_row_lower_zero_0

theorem active_row_lower_zero (i : Fin 214) (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition i))) :
    fixedSourceMatrix (activePosition i) (colOrder j) = 0 := by
  fin_cases i
  case «0» => exact active_row_lower_zero_0 j h
  case «1» => exact active_row_lower_zero_1 j h
  case «2» => exact active_row_lower_zero_2 j h
  case «3» => exact active_row_lower_zero_3 j h
  case «4» => exact active_row_lower_zero_4 j h
  case «5» => exact active_row_lower_zero_5 j h
  case «6» => exact active_row_lower_zero_6 j h
  case «7» => exact active_row_lower_zero_7 j h
  case «8» => exact active_row_lower_zero_8 j h
  case «9» => exact active_row_lower_zero_9 j h
  case «10» => exact active_row_lower_zero_10 j h
  case «11» => exact active_row_lower_zero_11 j h
  case «12» => exact active_row_lower_zero_12 j h
  case «13» => exact active_row_lower_zero_13 j h
  case «14» => exact active_row_lower_zero_14 j h
  case «15» => exact active_row_lower_zero_15 j h
  case «16» => exact active_row_lower_zero_16 j h
  case «17» => exact active_row_lower_zero_17 j h
  case «18» => exact active_row_lower_zero_18 j h
  case «19» => exact active_row_lower_zero_19 j h
  case «20» => exact active_row_lower_zero_20 j h
  case «21» => exact active_row_lower_zero_21 j h
  case «22» => exact active_row_lower_zero_22 j h
  case «23» => exact active_row_lower_zero_23 j h
  case «24» => exact active_row_lower_zero_24 j h
  case «25» => exact active_row_lower_zero_25 j h
  case «26» => exact active_row_lower_zero_26 j h
  case «27» => exact active_row_lower_zero_27 j h
  case «28» => exact active_row_lower_zero_28 j h
  case «29» => exact active_row_lower_zero_29 j h
  case «30» => exact active_row_lower_zero_30 j h
  case «31» => exact active_row_lower_zero_31 j h
  case «32» => exact active_row_lower_zero_32 j h
  case «33» => exact active_row_lower_zero_33 j h
  case «34» => exact active_row_lower_zero_34 j h
  case «35» => exact active_row_lower_zero_35 j h
  case «36» => exact active_row_lower_zero_36 j h
  case «37» => exact active_row_lower_zero_37 j h
  case «38» => exact active_row_lower_zero_38 j h
  case «39» => exact active_row_lower_zero_39 j h
  case «40» => exact active_row_lower_zero_40 j h
  case «41» => exact active_row_lower_zero_41 j h
  case «42» => exact active_row_lower_zero_42 j h
  case «43» => exact active_row_lower_zero_43 j h
  case «44» => exact active_row_lower_zero_44 j h
  case «45» => exact active_row_lower_zero_45 j h
  case «46» => exact active_row_lower_zero_46 j h
  case «47» => exact active_row_lower_zero_47 j h
  case «48» => exact active_row_lower_zero_48 j h
  case «49» => exact active_row_lower_zero_49 j h
  case «50» => exact active_row_lower_zero_50 j h
  case «51» => exact active_row_lower_zero_51 j h
  case «52» => exact active_row_lower_zero_52 j h
  case «53» => exact active_row_lower_zero_53 j h
  case «54» => exact active_row_lower_zero_54 j h
  case «55» => exact active_row_lower_zero_55 j h
  case «56» => exact active_row_lower_zero_56 j h
  case «57» => exact active_row_lower_zero_57 j h
  case «58» => exact active_row_lower_zero_58 j h
  case «59» => exact active_row_lower_zero_59 j h
  case «60» => exact active_row_lower_zero_60 j h
  case «61» => exact active_row_lower_zero_61 j h
  case «62» => exact active_row_lower_zero_62 j h
  case «63» => exact active_row_lower_zero_63 j h
  case «64» => exact active_row_lower_zero_64 j h
  case «65» => exact active_row_lower_zero_65 j h
  case «66» => exact active_row_lower_zero_66 j h
  case «67» => exact active_row_lower_zero_67 j h
  case «68» => exact active_row_lower_zero_68 j h
  case «69» => exact active_row_lower_zero_69 j h
  case «70» => exact active_row_lower_zero_70 j h
  case «71» => exact active_row_lower_zero_71 j h
  case «72» => exact active_row_lower_zero_72 j h
  case «73» => exact active_row_lower_zero_73 j h
  case «74» => exact active_row_lower_zero_74 j h
  case «75» => exact active_row_lower_zero_75 j h
  case «76» => exact active_row_lower_zero_76 j h
  case «77» => exact active_row_lower_zero_77 j h
  case «78» => exact active_row_lower_zero_78 j h
  case «79» => exact active_row_lower_zero_79 j h
  case «80» => exact active_row_lower_zero_80 j h
  case «81» => exact active_row_lower_zero_81 j h
  case «82» => exact active_row_lower_zero_82 j h
  case «83» => exact active_row_lower_zero_83 j h
  case «84» => exact active_row_lower_zero_84 j h
  case «85» => exact active_row_lower_zero_85 j h
  case «86» => exact active_row_lower_zero_86 j h
  case «87» => exact active_row_lower_zero_87 j h
  case «88» => exact active_row_lower_zero_88 j h
  case «89» => exact active_row_lower_zero_89 j h
  case «90» => exact active_row_lower_zero_90 j h
  case «91» => exact active_row_lower_zero_91 j h
  case «92» => exact active_row_lower_zero_92 j h
  case «93» => exact active_row_lower_zero_93 j h
  case «94» => exact active_row_lower_zero_94 j h
  case «95» => exact active_row_lower_zero_95 j h
  case «96» => exact active_row_lower_zero_96 j h
  case «97» => exact active_row_lower_zero_97 j h
  case «98» => exact active_row_lower_zero_98 j h
  case «99» => exact active_row_lower_zero_99 j h
  case «100» => exact active_row_lower_zero_100 j h
  case «101» => exact active_row_lower_zero_101 j h
  case «102» => exact active_row_lower_zero_102 j h
  case «103» => exact active_row_lower_zero_103 j h
  case «104» => exact active_row_lower_zero_104 j h
  case «105» => exact active_row_lower_zero_105 j h
  case «106» => exact active_row_lower_zero_106 j h
  case «107» => exact active_row_lower_zero_107 j h
  case «108» => exact active_row_lower_zero_108 j h
  case «109» => exact active_row_lower_zero_109 j h
  case «110» => exact active_row_lower_zero_110 j h
  case «111» => exact active_row_lower_zero_111 j h
  case «112» => exact active_row_lower_zero_112 j h
  case «113» => exact active_row_lower_zero_113 j h
  case «114» => exact active_row_lower_zero_114 j h
  case «115» => exact active_row_lower_zero_115 j h
  case «116» => exact active_row_lower_zero_116 j h
  case «117» => exact active_row_lower_zero_117 j h
  case «118» => exact active_row_lower_zero_118 j h
  case «119» => exact active_row_lower_zero_119 j h
  case «120» => exact active_row_lower_zero_120 j h
  case «121» => exact active_row_lower_zero_121 j h
  case «122» => exact active_row_lower_zero_122 j h
  case «123» => exact active_row_lower_zero_123 j h
  case «124» => exact active_row_lower_zero_124 j h
  case «125» => exact active_row_lower_zero_125 j h
  case «126» => exact active_row_lower_zero_126 j h
  case «127» => exact active_row_lower_zero_127 j h
  case «128» => exact active_row_lower_zero_128 j h
  case «129» => exact active_row_lower_zero_129 j h
  case «130» => exact active_row_lower_zero_130 j h
  case «131» => exact active_row_lower_zero_131 j h
  case «132» => exact active_row_lower_zero_132 j h
  case «133» => exact active_row_lower_zero_133 j h
  case «134» => exact active_row_lower_zero_134 j h
  case «135» => exact active_row_lower_zero_135 j h
  case «136» => exact active_row_lower_zero_136 j h
  case «137» => exact active_row_lower_zero_137 j h
  case «138» => exact active_row_lower_zero_138 j h
  case «139» => exact active_row_lower_zero_139 j h
  case «140» => exact active_row_lower_zero_140 j h
  case «141» => exact active_row_lower_zero_141 j h
  case «142» => exact active_row_lower_zero_142 j h
  case «143» => exact active_row_lower_zero_143 j h
  case «144» => exact active_row_lower_zero_144 j h
  case «145» => exact active_row_lower_zero_145 j h
  case «146» => exact active_row_lower_zero_146 j h
  case «147» => exact active_row_lower_zero_147 j h
  case «148» => exact active_row_lower_zero_148 j h
  case «149» => exact active_row_lower_zero_149 j h
  case «150» => exact active_row_lower_zero_150 j h
  case «151» => exact active_row_lower_zero_151 j h
  case «152» => exact active_row_lower_zero_152 j h
  case «153» => exact active_row_lower_zero_153 j h
  case «154» => exact active_row_lower_zero_154 j h
  case «155» => exact active_row_lower_zero_155 j h
  case «156» => exact active_row_lower_zero_156 j h
  case «157» => exact active_row_lower_zero_157 j h
  case «158» => exact active_row_lower_zero_158 j h
  case «159» => exact active_row_lower_zero_159 j h
  case «160» => exact active_row_lower_zero_160 j h
  case «161» => exact active_row_lower_zero_161 j h
  case «162» => exact active_row_lower_zero_162 j h
  case «163» => exact active_row_lower_zero_163 j h
  case «164» => exact active_row_lower_zero_164 j h
  case «165» => exact active_row_lower_zero_165 j h
  case «166» => exact active_row_lower_zero_166 j h
  case «167» => exact active_row_lower_zero_167 j h
  case «168» => exact active_row_lower_zero_168 j h
  case «169» => exact active_row_lower_zero_169 j h
  case «170» => exact active_row_lower_zero_170 j h
  case «171» => exact active_row_lower_zero_171 j h
  case «172» => exact active_row_lower_zero_172 j h
  case «173» => exact active_row_lower_zero_173 j h
  case «174» => exact active_row_lower_zero_174 j h
  case «175» => exact active_row_lower_zero_175 j h
  case «176» => exact active_row_lower_zero_176 j h
  case «177» => exact active_row_lower_zero_177 j h
  case «178» => exact active_row_lower_zero_178 j h
  case «179» => exact active_row_lower_zero_179 j h
  case «180» => exact active_row_lower_zero_180 j h
  case «181» => exact active_row_lower_zero_181 j h
  case «182» => exact active_row_lower_zero_182 j h
  case «183» => exact active_row_lower_zero_183 j h
  case «184» => exact active_row_lower_zero_184 j h
  case «185» => exact active_row_lower_zero_185 j h
  case «186» => exact active_row_lower_zero_186 j h
  case «187» => exact active_row_lower_zero_187 j h
  case «188» => exact active_row_lower_zero_188 j h
  case «189» => exact active_row_lower_zero_189 j h
  case «190» => exact active_row_lower_zero_190 j h
  case «191» => exact active_row_lower_zero_191 j h
  case «192» => exact active_row_lower_zero_192 j h
  case «193» => exact active_row_lower_zero_193 j h
  case «194» => exact active_row_lower_zero_194 j h
  case «195» => exact active_row_lower_zero_195 j h
  case «196» => exact active_row_lower_zero_196 j h
  case «197» => exact active_row_lower_zero_197 j h
  case «198» => exact active_row_lower_zero_198 j h
  case «199» => exact active_row_lower_zero_199 j h
  case «200» => exact active_row_lower_zero_200 j h
  case «201» => exact active_row_lower_zero_201 j h
  case «202» => exact active_row_lower_zero_202 j h
  case «203» => exact active_row_lower_zero_203 j h
  case «204» => exact active_row_lower_zero_204 j h
  case «205» => exact active_row_lower_zero_205 j h
  case «206» => exact active_row_lower_zero_206 j h
  case «207» => exact active_row_lower_zero_207 j h
  case «208» => exact active_row_lower_zero_208 j h
  case «209» => exact active_row_lower_zero_209 j h
  case «210» => exact active_row_lower_zero_210 j h
  case «211» => exact active_row_lower_zero_211 j h
  case «212» => exact active_row_lower_zero_212 j h
  case «213» => exact active_row_lower_zero_213 j h

#print axioms active_row_lower_zero
end
end AspisV8R19.R823ActiveLowerZeroDispatcher
