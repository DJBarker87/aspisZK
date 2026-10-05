import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk06
import AspisV8R19.R806Point02SelectedChunk07
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2StaticChunk02
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk06
open AspisV8R19.R806Point02SelectedChunk07
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem static_p2_d053_s0_flat51 : fixedSourceMatrix (pointPosition 2) (⟨45,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 53 0 (.inr (.inl 2)) = 0
  exact p2_d053_s0_flat51
#print axioms static_p2_d053_s0_flat51

theorem static_p2_d053_s1_flat52 : fixedSourceMatrix (pointPosition 2) (⟨46,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 53 1 (.inr (.inl 2)) = 0
  exact p2_d053_s1_flat52
#print axioms static_p2_d053_s1_flat52

theorem static_p2_d054_s0_flat53 : fixedSourceMatrix (pointPosition 2) (⟨47,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 54 0 (.inr (.inl 2)) = 0
  exact p2_d054_s0_flat53
#print axioms static_p2_d054_s0_flat53

theorem static_p2_d054_s1_flat54 : fixedSourceMatrix (pointPosition 2) (⟨48,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 54 1 (.inr (.inl 2)) = 0
  exact p2_d054_s1_flat54
#print axioms static_p2_d054_s1_flat54

theorem static_p2_d055_s0_flat55 : fixedSourceMatrix (pointPosition 2) (⟨49,by decide⟩ : Fin 222) = 536870908 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 55 0 (.inr (.inl 2)) = 536870908
  exact p2_d055_s0_flat55
#print axioms static_p2_d055_s0_flat55

theorem static_p2_d055_s1_flat56 : fixedSourceMatrix (pointPosition 2) (⟨50,by decide⟩ : Fin 222) = 536870908 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 55 1 (.inr (.inl 2)) = 536870908
  exact p2_d055_s1_flat56
#print axioms static_p2_d055_s1_flat56

theorem static_p2_d056_s0_flat57 : fixedSourceMatrix (pointPosition 2) (⟨51,by decide⟩ : Fin 222) = 586 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 56 0 (.inr (.inl 2)) = 586
  exact p2_d056_s0_flat57
#print axioms static_p2_d056_s0_flat57

theorem static_p2_d056_s1_flat58 : fixedSourceMatrix (pointPosition 2) (⟨52,by decide⟩ : Fin 222) = 4534 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 56 1 (.inr (.inl 2)) = 4534
  exact p2_d056_s1_flat58
#print axioms static_p2_d056_s1_flat58

end
end AspisV8R19.R812SourceBlock06P2StaticChunk02
