import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806Point02SelectedChunk04
import AspisV8R19.R806Point02SelectedChunk05
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P0StaticChunk00
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R804LiteralSourceRow114 AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R806Point02SelectedChunk04
open AspisV8R19.R806Point02SelectedChunk05
noncomputable section
local instance : Nontrivial R807SourceBlock01Binding.M := ⟨⟨0,1,by decide⟩⟩

theorem static_p0_d028_s1_flat35 : fixedSourceMatrix (pointPosition 0) (⟨0,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 28 1 (.inr (.inl 0)) = 0
  exact p0_d028_s1_flat35
#print axioms static_p0_d028_s1_flat35

theorem static_p0_d029_s0_flat36 : fixedSourceMatrix (pointPosition 0) (⟨1,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 29 0 (.inr (.inl 0)) = 0
  exact p0_d029_s0_flat36
#print axioms static_p0_d029_s0_flat36

theorem static_p0_d029_s1_flat37 : fixedSourceMatrix (pointPosition 0) (⟨2,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 29 1 (.inr (.inl 0)) = 0
  exact p0_d029_s1_flat37
#print axioms static_p0_d029_s1_flat37

theorem static_p0_d030_s0_flat38 : fixedSourceMatrix (pointPosition 0) (⟨3,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 30 0 (.inr (.inl 0)) = 0
  exact p0_d030_s0_flat38
#print axioms static_p0_d030_s0_flat38

theorem static_p0_d030_s1_flat39 : fixedSourceMatrix (pointPosition 0) (⟨4,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 30 1 (.inr (.inl 0)) = 0
  exact p0_d030_s1_flat39
#print axioms static_p0_d030_s1_flat39

theorem static_p0_d031_s0_flat40 : fixedSourceMatrix (pointPosition 0) (⟨5,by decide⟩ : Fin 222) = 4320 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 31 0 (.inr (.inl 0)) = 4320
  exact p0_d031_s0_flat40
#print axioms static_p0_d031_s0_flat40

theorem static_p0_d031_s1_flat41 : fixedSourceMatrix (pointPosition 0) (⟨6,by decide⟩ : Fin 222) = 21888 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 31 1 (.inr (.inl 0)) = 21888
  exact p0_d031_s1_flat41
#print axioms static_p0_d031_s1_flat41

theorem static_p0_d048_s1_flat42 : fixedSourceMatrix (pointPosition 0) (⟨36,by decide⟩ : Fin 222) = 0 := by
  unfold fixedSourceMatrix
  rw [literalSourceMatrix_point_entry]
  change sparseObservation (1073741824:R807SourceBlock01Binding.M) (536870912:R807SourceBlock01Binding.M) 7 5 (-5) 5 0 7 z 48 1 (.inr (.inl 0)) = 0
  exact p0_d048_s1_flat42
#print axioms static_p0_d048_s1_flat42

end
end AspisV8R19.R812SourceBlock06P0StaticChunk00
