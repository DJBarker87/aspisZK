import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk01
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2StaticLowChunk01
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk01
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem static_p2_d044_s1_flat08 : fixedSourceMatrix (pointPosition 2) (⟨32,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 44 1 (.inr (.inl 2)) = 0
  exact p2_d044_s1_flat08
#print axioms static_p2_d044_s1_flat08

theorem static_p2_d045_s0_flat09 : fixedSourceMatrix (pointPosition 2) (⟨33,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 45 0 (.inr (.inl 2)) = 0
  exact p2_d045_s0_flat09
#print axioms static_p2_d045_s0_flat09

theorem static_p2_d040_s0_flat10 : fixedSourceMatrix (pointPosition 2) (⟨23,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 40 0 (.inr (.inl 2)) = 0
  exact p2_d040_s0_flat10
#print axioms static_p2_d040_s0_flat10

theorem static_p2_d040_s1_flat11 : fixedSourceMatrix (pointPosition 2) (⟨24,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 40 1 (.inr (.inl 2)) = 0
  exact p2_d040_s1_flat11
#print axioms static_p2_d040_s1_flat11

theorem static_p2_d041_s0_flat12 : fixedSourceMatrix (pointPosition 2) (⟨25,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 41 0 (.inr (.inl 2)) = 0
  exact p2_d041_s0_flat12
#print axioms static_p2_d041_s0_flat12

theorem static_p2_d041_s1_flat13 : fixedSourceMatrix (pointPosition 2) (⟨26,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 41 1 (.inr (.inl 2)) = 0
  exact p2_d041_s1_flat13
#print axioms static_p2_d041_s1_flat13

theorem static_p2_d042_s0_flat14 : fixedSourceMatrix (pointPosition 2) (⟨27,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 42 0 (.inr (.inl 2)) = 0
  exact p2_d042_s0_flat14
#print axioms static_p2_d042_s0_flat14

theorem static_p2_d042_s1_flat15 : fixedSourceMatrix (pointPosition 2) (⟨28,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 42 1 (.inr (.inl 2)) = 0
  exact p2_d042_s1_flat15
#print axioms static_p2_d042_s1_flat15

end
end AspisV8R19.R812SourceBlock06P2StaticLowChunk01
