import AspisV8R19.R807SourceBlock01Binding
import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R780Point02WeightPrototype
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk03P2
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2Entry00
open AspisV8R19.R807SourceBlock01Binding AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R780Point02WeightPrototype AspisV8R19.R780Point02WeightChunk00P2 AspisV8R19.R780Point02WeightChunk03P2
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by funext i; fin_cases i <;> rfl
theorem source_block06_p2_entry00 :
  diagonalSourceBlock 6 (⟨37,by decide⟩ : Fin (blockSize 6)) (⟨0,by decide⟩ : Fin 39) =
    R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨0,by decide⟩ : Fin 39) := by
  simp only [diagonalSourceBlock, reorderedSourceMatrix, Matrix.submatrix_apply]
  change fixedSourceMatrix (rowOrder (flatIndex 6 (⟨37,by decide⟩ : Fin (blockSize 6)))) (colOrder (flatIndex 6 (⟨0,by decide⟩ : Fin 39))) = _
  change literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨0,by decide⟩ : Fin 39))) = _
  rw [literalSourceMatrix_point_entry, z_eq_zFin10]
  unfold sparseObservation
  change (pw2 114 - 7^(1+1)*pw2 112) - (pw2 2 - 7^(1+1)*pw2 0) = _
  rw [pw2_0114, pw2_0112, pw2_0002, pw2_0000]
  decide
#print axioms source_block06_p2_entry00
end
end AspisV8R19.R812SourceBlock06P2Entry00
