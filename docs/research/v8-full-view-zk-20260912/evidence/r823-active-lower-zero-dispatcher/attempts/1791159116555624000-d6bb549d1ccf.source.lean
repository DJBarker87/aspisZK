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

theorem active_row_lower_zero (i : Fin 214) (j : Fin 222)
    (h : blockLabel j < blockLabel (rowOrderInv (activePosition i))) :
    fixedSourceMatrix (activePosition i) (colOrder j) = 0 := by
  fin_cases i
  case «0» =>
    let flat : Fin 222 := ⟨35, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨0, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroPrototype.rowFlat35_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨0, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «1» =>
    let flat : Fin 222 := ⟨36, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨1, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat36_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨1, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «2» =>
    let flat : Fin 222 := ⟨37, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨2, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat37_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨2, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «3» =>
    let flat : Fin 222 := ⟨38, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨3, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat38_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨3, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «4» =>
    let flat : Fin 222 := ⟨39, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨4, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk01.rowFlat39_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨4, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «5» =>
    let flat : Fin 222 := ⟨40, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨5, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat40_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨5, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «6» =>
    let flat : Fin 222 := ⟨41, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨6, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat41_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨6, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «7» =>
    let flat : Fin 222 := ⟨18, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨7, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat18_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨7, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «8» =>
    let flat : Fin 222 := ⟨19, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨8, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk02.rowFlat19_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨8, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «9» =>
    let flat : Fin 222 := ⟨20, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨9, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat20_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨9, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «10» =>
    let flat : Fin 222 := ⟨21, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨10, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat21_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨10, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «11» =>
    let flat : Fin 222 := ⟨22, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨11, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat22_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨11, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «12» =>
    let flat : Fin 222 := ⟨23, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨12, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk03.rowFlat23_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨12, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «13» =>
    let flat : Fin 222 := ⟨24, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨13, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat24_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨13, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «14» =>
    let flat : Fin 222 := ⟨25, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨14, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat25_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨14, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «15» =>
    let flat : Fin 222 := ⟨26, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨15, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat26_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨15, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «16» =>
    let flat : Fin 222 := ⟨27, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨16, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk04.rowFlat27_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨16, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «17» =>
    let flat : Fin 222 := ⟨28, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨17, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat28_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨17, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «18» =>
    let flat : Fin 222 := ⟨29, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨18, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat29_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨18, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «19» =>
    let flat : Fin 222 := ⟨30, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨19, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat30_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨19, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «20» =>
    let flat : Fin 222 := ⟨31, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨20, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk05.rowFlat31_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨20, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «21» =>
    let flat : Fin 222 := ⟨32, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨21, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat32_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨21, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «22» =>
    let flat : Fin 222 := ⟨33, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨22, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat33_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨22, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «23» =>
    let flat : Fin 222 := ⟨10, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨23, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat10_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨23, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «24» =>
    let flat : Fin 222 := ⟨11, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨24, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk06.rowFlat11_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨24, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «25» =>
    let flat : Fin 222 := ⟨12, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨25, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat12_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨25, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «26» =>
    let flat : Fin 222 := ⟨13, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨26, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat13_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨26, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «27» =>
    let flat : Fin 222 := ⟨14, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨27, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat14_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨27, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «28» =>
    let flat : Fin 222 := ⟨15, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨28, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk07.rowFlat15_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨28, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «29» =>
    let flat : Fin 222 := ⟨16, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨29, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat16_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨29, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «30» =>
    let flat : Fin 222 := ⟨17, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨30, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat17_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨30, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «31» =>
    let flat : Fin 222 := ⟨7, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨31, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat7_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨31, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «32» =>
    let flat : Fin 222 := ⟨8, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨32, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk08.rowFlat8_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨32, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «33» =>
    let flat : Fin 222 := ⟨9, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨33, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat9_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨33, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «34» =>
    let flat : Fin 222 := ⟨6, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨34, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat6_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨34, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «35» =>
    let flat : Fin 222 := ⟨34, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨35, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat34_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨35, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «36» =>
    let flat : Fin 222 := ⟨42, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨36, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk09.rowFlat42_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨36, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «37» =>
    let flat : Fin 222 := ⟨43, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨37, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat43_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨37, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «38» =>
    let flat : Fin 222 := ⟨44, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨38, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat44_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨38, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «39» =>
    let flat : Fin 222 := ⟨45, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨39, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat45_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨39, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «40» =>
    let flat : Fin 222 := ⟨46, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨40, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk10.rowFlat46_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨40, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «41» =>
    let flat : Fin 222 := ⟨47, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨41, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat47_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨41, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «42» =>
    let flat : Fin 222 := ⟨48, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨42, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat48_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨42, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «43» =>
    let flat : Fin 222 := ⟨49, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨43, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat49_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨43, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «44» =>
    let flat : Fin 222 := ⟨50, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨44, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk11.rowFlat50_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨44, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «45» =>
    let flat : Fin 222 := ⟨51, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨45, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat51_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨45, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «46» =>
    let flat : Fin 222 := ⟨52, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨46, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat52_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨46, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «47» =>
    let flat : Fin 222 := ⟨53, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨47, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat53_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨47, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «48» =>
    let flat : Fin 222 := ⟨54, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨48, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk12.rowFlat54_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨48, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «49» =>
    let flat : Fin 222 := ⟨55, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨49, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat55_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨49, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «50» =>
    let flat : Fin 222 := ⟨56, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨50, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat56_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨50, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «51» =>
    let flat : Fin 222 := ⟨57, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨51, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat57_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨51, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «52» =>
    let flat : Fin 222 := ⟨58, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨52, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk13.rowFlat58_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨52, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «53» =>
    let flat : Fin 222 := ⟨59, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨53, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat59_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨53, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «54» =>
    let flat : Fin 222 := ⟨60, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨54, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat60_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨54, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «55» =>
    let flat : Fin 222 := ⟨61, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨55, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat61_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨55, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «56» =>
    let flat : Fin 222 := ⟨62, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨56, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk14.rowFlat62_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨56, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «57» =>
    let flat : Fin 222 := ⟨63, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨57, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat63_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨57, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «58» =>
    let flat : Fin 222 := ⟨64, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨58, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat64_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨58, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «59» =>
    let flat : Fin 222 := ⟨65, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨59, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat65_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨59, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «60» =>
    let flat : Fin 222 := ⟨66, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨60, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk15.rowFlat66_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨60, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «61» =>
    let flat : Fin 222 := ⟨67, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨61, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat67_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨61, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «62» =>
    let flat : Fin 222 := ⟨68, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨62, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat68_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨62, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «63» =>
    let flat : Fin 222 := ⟨69, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨63, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat69_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨63, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «64» =>
    let flat : Fin 222 := ⟨70, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨64, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk16.rowFlat70_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨64, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «65» =>
    let flat : Fin 222 := ⟨71, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨65, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat71_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨65, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «66» =>
    let flat : Fin 222 := ⟨84, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨66, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat84_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨66, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «67» =>
    let flat : Fin 222 := ⟨85, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨67, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat85_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨67, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «68» =>
    let flat : Fin 222 := ⟨86, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨68, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk17.rowFlat86_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨68, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «69» =>
    let flat : Fin 222 := ⟨87, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨69, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat87_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨69, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «70» =>
    let flat : Fin 222 := ⟨88, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨70, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat88_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨70, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «71» =>
    let flat : Fin 222 := ⟨89, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨71, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat89_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨71, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «72» =>
    let flat : Fin 222 := ⟨90, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨72, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk18.rowFlat90_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨72, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «73» =>
    let flat : Fin 222 := ⟨91, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨73, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat91_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨73, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «74» =>
    let flat : Fin 222 := ⟨92, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨74, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat92_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨74, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «75» =>
    let flat : Fin 222 := ⟨93, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨75, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat93_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨75, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «76» =>
    let flat : Fin 222 := ⟨94, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨76, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk19.rowFlat94_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨76, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «77» =>
    let flat : Fin 222 := ⟨95, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨77, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat95_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨77, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «78» =>
    let flat : Fin 222 := ⟨96, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨78, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat96_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨78, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «79» =>
    let flat : Fin 222 := ⟨97, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨79, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat97_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨79, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «80» =>
    let flat : Fin 222 := ⟨98, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨80, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk20.rowFlat98_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨80, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «81» =>
    let flat : Fin 222 := ⟨99, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨81, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat99_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨81, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «82» =>
    let flat : Fin 222 := ⟨76, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨82, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat76_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨82, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «83» =>
    let flat : Fin 222 := ⟨77, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨83, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat77_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨83, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «84» =>
    let flat : Fin 222 := ⟨78, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨84, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk21.rowFlat78_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨84, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «85» =>
    let flat : Fin 222 := ⟨79, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨85, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat79_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨85, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «86» =>
    let flat : Fin 222 := ⟨80, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨86, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat80_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨86, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «87» =>
    let flat : Fin 222 := ⟨81, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨87, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat81_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨87, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «88» =>
    let flat : Fin 222 := ⟨82, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨88, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk22.rowFlat82_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨88, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «89» =>
    let flat : Fin 222 := ⟨83, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨89, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat83_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨89, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «90» =>
    let flat : Fin 222 := ⟨74, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨90, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat74_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨90, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «91» =>
    let flat : Fin 222 := ⟨75, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨91, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat75_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨91, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «92» =>
    let flat : Fin 222 := ⟨125, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨92, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk23.rowFlat125_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨92, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «93» =>
    let flat : Fin 222 := ⟨121, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨93, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat121_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨93, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «94» =>
    let flat : Fin 222 := ⟨122, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨94, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat122_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨94, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «95» =>
    let flat : Fin 222 := ⟨123, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨95, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat123_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨95, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «96» =>
    let flat : Fin 222 := ⟨124, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨96, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk24.rowFlat124_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨96, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «97» =>
    let flat : Fin 222 := ⟨105, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨97, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat105_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨97, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «98» =>
    let flat : Fin 222 := ⟨106, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨98, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat106_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨98, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «99» =>
    let flat : Fin 222 := ⟨107, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨99, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat107_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨99, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «100» =>
    let flat : Fin 222 := ⟨108, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨100, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk25.rowFlat108_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨100, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «101» =>
    let flat : Fin 222 := ⟨109, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨101, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat109_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨101, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «102» =>
    let flat : Fin 222 := ⟨110, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨102, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat110_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨102, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «103» =>
    let flat : Fin 222 := ⟨111, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨103, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat111_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨103, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «104» =>
    let flat : Fin 222 := ⟨112, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨104, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk26.rowFlat112_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨104, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «105» =>
    let flat : Fin 222 := ⟨113, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨105, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat113_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨105, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «106» =>
    let flat : Fin 222 := ⟨114, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨106, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat114_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨106, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «107» =>
    let flat : Fin 222 := ⟨115, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨107, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat115_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨107, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «108» =>
    let flat : Fin 222 := ⟨116, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨108, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk27.rowFlat116_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨108, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «109» =>
    let flat : Fin 222 := ⟨117, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨109, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat117_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨109, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «110» =>
    let flat : Fin 222 := ⟨118, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨110, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat118_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨110, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «111» =>
    let flat : Fin 222 := ⟨119, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨111, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat119_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨111, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «112» =>
    let flat : Fin 222 := ⟨120, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨112, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk28.rowFlat120_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨112, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «113» =>
    let flat : Fin 222 := ⟨101, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨113, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat101_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨113, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «114» =>
    let flat : Fin 222 := ⟨102, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨114, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat102_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨114, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «115» =>
    let flat : Fin 222 := ⟨103, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨115, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat103_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨115, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «116» =>
    let flat : Fin 222 := ⟨104, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨116, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk29.rowFlat104_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨116, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «117» =>
    let flat : Fin 222 := ⟨100, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨117, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat100_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨117, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «118» =>
    let flat : Fin 222 := ⟨133, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨118, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat133_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨118, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «119» =>
    let flat : Fin 222 := ⟨134, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨119, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat134_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨119, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «120» =>
    let flat : Fin 222 := ⟨132, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨120, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk30.rowFlat132_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨120, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «121» =>
    let flat : Fin 222 := ⟨130, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨121, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat130_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨121, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «122» =>
    let flat : Fin 222 := ⟨131, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨122, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat131_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨122, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «123» =>
    let flat : Fin 222 := ⟨126, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨123, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat126_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨123, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «124» =>
    let flat : Fin 222 := ⟨127, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨124, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk31.rowFlat127_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨124, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «125» =>
    let flat : Fin 222 := ⟨128, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨125, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat128_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨125, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «126» =>
    let flat : Fin 222 := ⟨129, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨126, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat129_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨126, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «127» =>
    let flat : Fin 222 := ⟨141, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨127, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat141_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨127, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «128» =>
    let flat : Fin 222 := ⟨139, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨128, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk32.rowFlat139_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨128, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «129» =>
    let flat : Fin 222 := ⟨140, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨129, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat140_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨129, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «130» =>
    let flat : Fin 222 := ⟨135, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨130, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat135_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨130, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «131» =>
    let flat : Fin 222 := ⟨136, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨131, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat136_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨131, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «132» =>
    let flat : Fin 222 := ⟨137, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨132, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk33.rowFlat137_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨132, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «133» =>
    let flat : Fin 222 := ⟨138, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨133, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat138_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨133, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «134» =>
    let flat : Fin 222 := ⟨142, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨134, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat142_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨134, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «135» =>
    let flat : Fin 222 := ⟨143, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨135, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat143_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨135, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «136» =>
    let flat : Fin 222 := ⟨144, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨136, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk34.rowFlat144_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨136, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «137» =>
    let flat : Fin 222 := ⟨145, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨137, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat145_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨137, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «138» =>
    let flat : Fin 222 := ⟨146, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨138, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat146_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨138, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «139» =>
    let flat : Fin 222 := ⟨147, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨139, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat147_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨139, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «140» =>
    let flat : Fin 222 := ⟨148, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨140, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk35.rowFlat148_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨140, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «141» =>
    let flat : Fin 222 := ⟨149, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨141, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat149_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨141, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «142» =>
    let flat : Fin 222 := ⟨156, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨142, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat156_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨142, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «143» =>
    let flat : Fin 222 := ⟨154, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨143, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat154_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨143, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «144» =>
    let flat : Fin 222 := ⟨155, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨144, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk36.rowFlat155_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨144, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «145» =>
    let flat : Fin 222 := ⟨152, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨145, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat152_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨145, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «146» =>
    let flat : Fin 222 := ⟨153, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨146, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat153_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨146, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «147» =>
    let flat : Fin 222 := ⟨150, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨147, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat150_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨147, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «148» =>
    let flat : Fin 222 := ⟨151, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨148, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk37.rowFlat151_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨148, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «149» =>
    let flat : Fin 222 := ⟨163, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨149, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat163_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨149, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «150» =>
    let flat : Fin 222 := ⟨161, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨150, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat161_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨150, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «151» =>
    let flat : Fin 222 := ⟨162, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨151, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat162_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨151, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «152» =>
    let flat : Fin 222 := ⟨157, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨152, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk38.rowFlat157_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨152, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «153» =>
    let flat : Fin 222 := ⟨158, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨153, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat158_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨153, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «154» =>
    let flat : Fin 222 := ⟨159, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨154, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat159_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨154, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «155» =>
    let flat : Fin 222 := ⟨160, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨155, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat160_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨155, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «156» =>
    let flat : Fin 222 := ⟨188, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨156, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk39.rowFlat188_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨156, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «157» =>
    let flat : Fin 222 := ⟨189, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨157, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat189_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨157, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «158» =>
    let flat : Fin 222 := ⟨184, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨158, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat184_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨158, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «159» =>
    let flat : Fin 222 := ⟨185, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨159, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat185_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨159, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «160» =>
    let flat : Fin 222 := ⟨186, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨160, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk40.rowFlat186_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨160, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «161» =>
    let flat : Fin 222 := ⟨187, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨161, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat187_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨161, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «162» =>
    let flat : Fin 222 := ⟨176, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨162, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat176_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨162, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «163» =>
    let flat : Fin 222 := ⟨177, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨163, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat177_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨163, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «164» =>
    let flat : Fin 222 := ⟨178, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨164, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk41.rowFlat178_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨164, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «165» =>
    let flat : Fin 222 := ⟨179, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨165, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat179_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨165, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «166» =>
    let flat : Fin 222 := ⟨180, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨166, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat180_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨166, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «167» =>
    let flat : Fin 222 := ⟨181, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨167, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat181_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨167, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «168» =>
    let flat : Fin 222 := ⟨182, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨168, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk42.rowFlat182_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨168, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «169» =>
    let flat : Fin 222 := ⟨183, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨169, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat183_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨169, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «170» =>
    let flat : Fin 222 := ⟨168, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨170, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat168_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨170, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «171» =>
    let flat : Fin 222 := ⟨169, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨171, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat169_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨171, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «172» =>
    let flat : Fin 222 := ⟨170, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨172, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk43.rowFlat170_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨172, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «173» =>
    let flat : Fin 222 := ⟨171, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨173, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat171_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨173, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «174» =>
    let flat : Fin 222 := ⟨172, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨174, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat172_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨174, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «175» =>
    let flat : Fin 222 := ⟨173, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨175, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat173_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨175, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «176» =>
    let flat : Fin 222 := ⟨174, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨176, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk44.rowFlat174_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨176, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «177» =>
    let flat : Fin 222 := ⟨175, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨177, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat175_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨177, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «178» =>
    let flat : Fin 222 := ⟨166, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨178, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat166_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨178, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «179» =>
    let flat : Fin 222 := ⟨167, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨179, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat167_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨179, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «180» =>
    let flat : Fin 222 := ⟨164, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨180, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk45.rowFlat164_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨180, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «181» =>
    let flat : Fin 222 := ⟨165, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨181, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat165_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨181, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «182» =>
    let flat : Fin 222 := ⟨221, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨182, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat221_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨182, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «183» =>
    let flat : Fin 222 := ⟨205, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨183, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat205_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨183, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «184» =>
    let flat : Fin 222 := ⟨206, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨184, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk46.rowFlat206_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨184, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «185» =>
    let flat : Fin 222 := ⟨207, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨185, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat207_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨185, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «186» =>
    let flat : Fin 222 := ⟨208, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨186, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat208_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨186, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «187» =>
    let flat : Fin 222 := ⟨209, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨187, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat209_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨187, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «188» =>
    let flat : Fin 222 := ⟨210, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨188, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk47.rowFlat210_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨188, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «189» =>
    let flat : Fin 222 := ⟨211, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨189, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat211_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨189, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «190» =>
    let flat : Fin 222 := ⟨212, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨190, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat212_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨190, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «191» =>
    let flat : Fin 222 := ⟨213, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨191, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat213_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨191, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «192» =>
    let flat : Fin 222 := ⟨214, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨192, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk48.rowFlat214_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨192, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «193» =>
    let flat : Fin 222 := ⟨215, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨193, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat215_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨193, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «194» =>
    let flat : Fin 222 := ⟨216, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨194, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat216_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨194, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «195» =>
    let flat : Fin 222 := ⟨217, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨195, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat217_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨195, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «196» =>
    let flat : Fin 222 := ⟨218, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨196, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk49.rowFlat218_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨196, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «197» =>
    let flat : Fin 222 := ⟨219, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨197, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat219_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨197, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «198» =>
    let flat : Fin 222 := ⟨220, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨198, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat220_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨198, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «199» =>
    let flat : Fin 222 := ⟨197, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨199, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat197_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨199, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «200» =>
    let flat : Fin 222 := ⟨198, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨200, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk50.rowFlat198_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨200, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «201» =>
    let flat : Fin 222 := ⟨199, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨201, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat199_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨201, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «202» =>
    let flat : Fin 222 := ⟨200, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨202, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat200_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨202, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «203» =>
    let flat : Fin 222 := ⟨201, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨203, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat201_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨203, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «204» =>
    let flat : Fin 222 := ⟨202, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨204, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk51.rowFlat202_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨204, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «205» =>
    let flat : Fin 222 := ⟨203, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨205, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat203_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨205, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «206» =>
    let flat : Fin 222 := ⟨204, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨206, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat204_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨206, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «207» =>
    let flat : Fin 222 := ⟨193, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨207, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat193_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨207, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «208» =>
    let flat : Fin 222 := ⟨194, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨208, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk52.rowFlat194_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨208, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «209» =>
    let flat : Fin 222 := ⟨195, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨209, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat195_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨209, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «210» =>
    let flat : Fin 222 := ⟨196, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨210, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat196_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨210, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «211» =>
    let flat : Fin 222 := ⟨190, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨211, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat190_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨211, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «212» =>
    let flat : Fin 222 := ⟨191, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨212, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk53.rowFlat191_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨212, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr
  case «213» =>
    let flat : Fin 222 := ⟨192, by decide⟩
    have hflat : rowOrderInv (activePosition (⟨213, by decide⟩ : Fin 214)) = flat := by decide
    have hineq : blockLabel j < blockLabel flat := by simpa [flat, activePosition, rowOrderInv] using h
    have hr : reorderedSourceMatrix flat j = 0 := AspisV8R19.R811SourceLowerZeroChunk54.rowFlat192_lower_zero j hineq
    change fixedSourceMatrix (rowOrder flat) (colOrder j) = 0 at hr
    have hrow : rowOrder flat = activePosition (⟨213, by decide⟩ : Fin 214) := by
      rw [← hflat]
      exact row_right _
    rw [hrow] at hr
    simpa [activePosition] using hr

#print axioms active_row_lower_zero
end
end AspisV8R19.R823ActiveLowerZeroDispatcher
