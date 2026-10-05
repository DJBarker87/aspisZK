import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk04
import AspisV8R19.R806Point02SelectedChunk05
import AspisV8R19.R806Point02SelectedChunk06
import AspisV8R19.R806Point02SelectedChunk07
import AspisV8R19.R806Point02SelectedChunk08
import AspisV8R19.R806Point02SelectedChunk09
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2Row
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk04
open AspisV8R19.R806Point02SelectedChunk05
open AspisV8R19.R806Point02SelectedChunk06
open AspisV8R19.R806Point02SelectedChunk07
open AspisV8R19.R806Point02SelectedChunk08
open AspisV8R19.R806Point02SelectedChunk09
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩

theorem source_block06_p2_row (j : Fin 39) :
  diagonalSourceBlock 6 (⟨37,by decide⟩ : Fin (blockSize 6)) j = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) j := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  have hrow : rowOrder (flatIndex 6 (⟨37,by decide⟩ : Fin (blockSize 6))) = pointPosition (⟨2,by decide⟩ : Fin 3) := by decide
  rw [hrow]
  change literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 j)) = _
  rw [literalSourceMatrix_point_entry]
  fin_cases j
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 2)) = _
    exact p2_d028_s1_flat35
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 0 (.inr (.inl 2)) = _
    exact p2_d029_s0_flat36
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 29 1 (.inr (.inl 2)) = _
    exact p2_d029_s1_flat37
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 0 (.inr (.inl 2)) = _
    exact p2_d030_s0_flat38
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 30 1 (.inr (.inl 2)) = _
    exact p2_d030_s1_flat39
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 0 (.inr (.inl 2)) = _
    exact p2_d031_s0_flat40
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 31 1 (.inr (.inl 2)) = _
    exact p2_d031_s1_flat41
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 48 1 (.inr (.inl 2)) = _
    exact p2_d048_s1_flat42
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 0 (.inr (.inl 2)) = _
    exact p2_d049_s0_flat43
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 49 1 (.inr (.inl 2)) = _
    exact p2_d049_s1_flat44
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 0 (.inr (.inl 2)) = _
    exact p2_d050_s0_flat45
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 50 1 (.inr (.inl 2)) = _
    exact p2_d050_s1_flat46
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 0 (.inr (.inl 2)) = _
    exact p2_d051_s0_flat47
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 51 1 (.inr (.inl 2)) = _
    exact p2_d051_s1_flat48
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 0 (.inr (.inl 2)) = _
    exact p2_d052_s0_flat49
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 52 1 (.inr (.inl 2)) = _
    exact p2_d052_s1_flat50
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 0 (.inr (.inl 2)) = _
    exact p2_d053_s0_flat51
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 53 1 (.inr (.inl 2)) = _
    exact p2_d053_s1_flat52
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 0 (.inr (.inl 2)) = _
    exact p2_d054_s0_flat53
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 54 1 (.inr (.inl 2)) = _
    exact p2_d054_s1_flat54
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 0 (.inr (.inl 2)) = _
    exact p2_d055_s0_flat55
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 55 1 (.inr (.inl 2)) = _
    exact p2_d055_s1_flat56
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 0 (.inr (.inl 2)) = _
    exact p2_d056_s0_flat57
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 56 1 (.inr (.inl 2)) = _
    exact p2_d056_s1_flat58
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 0 (.inr (.inl 2)) = _
    exact p2_d057_s0_flat59
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 57 1 (.inr (.inl 2)) = _
    exact p2_d057_s1_flat60
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 0 (.inr (.inl 2)) = _
    exact p2_d058_s0_flat61
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 58 1 (.inr (.inl 2)) = _
    exact p2_d058_s1_flat62
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 0 (.inr (.inl 2)) = _
    exact p2_d059_s0_flat63
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 59 1 (.inr (.inl 2)) = _
    exact p2_d059_s1_flat64
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 0 (.inr (.inl 2)) = _
    exact p2_d060_s0_flat65
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 60 2 (.inr (.inl 2)) = _
    exact p2_d060_s2_flat66
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 0 (.inr (.inl 2)) = _
    exact p2_d061_s0_flat67
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 61 2 (.inr (.inl 2)) = _
    exact p2_d061_s2_flat68
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 0 (.inr (.inl 2)) = _
    exact p2_d062_s0_flat69
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 62 2 (.inr (.inl 2)) = _
    exact p2_d062_s2_flat70
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 63 0 (.inr (.inl 2)) = _
    exact p2_d063_s0_flat71
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 27 2 (.inr (.inl 2)) = _
    exact p2_d027_s2_flat72
  · change sparseObservation (1073741824:M) (536870912:M) 7 5 (-5) 5 0 7 z 47 2 (.inr (.inl 2)) = _
    exact p2_d047_s2_flat73
#print axioms source_block06_p2_row
end
end AspisV8R19.R812SourceBlock06P2Row
