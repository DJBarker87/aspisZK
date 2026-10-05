import AspisV8R19.R747JointBlock39Preflight
import AspisV8R19.R803LiteralSupplementaryEntries
import AspisV8R19.R806LiteralBlockLayout
import AspisV8R19.R724BlockOrderMaps
import AspisV8R19.R780Point02WeightChunk00P2
import AspisV8R19.R780Point02WeightChunk03P2
import AspisV8R19.R780Point02WeightChunk04P2
import AspisV8R19.R780Point02WeightChunk05P2
import AspisV8R19.R780Point02WeightChunk06P2
import AspisV8R19.R780Point02WeightChunk17P2
import AspisV8R19.R780Point02WeightChunk18P2
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 32768
namespace AspisV8R19.R812SourceBlock06P2DirectChunk00
open AspisV8R19.R806LiteralBlockLayout AspisV8R19.R724BlockOrderMaps
open AspisV8R19.R799LiteralSourceMatrix AspisV8R19.R803LiteralSupplementaryEntries AspisV8R19.R748JointWitnessPointEntry AspisV8R19.R743JointSparseEntryBinding
open AspisV8R19.R780Point02WeightChunk00P2
open AspisV8R19.R780Point02WeightChunk03P2
open AspisV8R19.R780Point02WeightChunk04P2
open AspisV8R19.R780Point02WeightChunk05P2
open AspisV8R19.R780Point02WeightChunk06P2
open AspisV8R19.R780Point02WeightChunk17P2
open AspisV8R19.R780Point02WeightChunk18P2
noncomputable section
abbrev M := ZMod 2147483647
local instance : Nontrivial M := ⟨⟨0,1,by decide⟩⟩
lemma z_eq_zFin10 : z = AspisR19.R750WitnessPointSupport.zFin10 (F := M) := by funext i; fin_cases i <;> rfl

theorem direct_p2_d028_s1_flat35 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨0,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨0,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 114 - 7^(1+1)*pw2 112) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0114, pw2_0112, pw2_0002, pw2_0000]
  decide
#print axioms direct_p2_d028_s1_flat35

theorem direct_p2_d029_s0_flat36 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨1,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨1,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 117 - 7^(0+1)*pw2 116) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0117, pw2_0116, pw2_0001, pw2_0000]
  decide
#print axioms direct_p2_d029_s0_flat36

theorem direct_p2_d029_s1_flat37 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨2,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨2,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 118 - 7^(1+1)*pw2 116) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0118, pw2_0116, pw2_0002, pw2_0000]
  decide
#print axioms direct_p2_d029_s1_flat37

theorem direct_p2_d030_s0_flat38 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨3,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨3,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 121 - 7^(0+1)*pw2 120) - (pw2 1 - 7^(0+1)*pw2 0) = 0
  rw [pw2_0121, pw2_0120, pw2_0001, pw2_0000]
  decide
#print axioms direct_p2_d030_s0_flat38

theorem direct_p2_d030_s1_flat39 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨4,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨4,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 122 - 7^(1+1)*pw2 120) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0122, pw2_0120, pw2_0002, pw2_0000]
  decide
#print axioms direct_p2_d030_s1_flat39

theorem direct_p2_d031_s0_flat40 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨5,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨5,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 125 - 7^(0+1)*pw2 124) - (pw2 1 - 7^(0+1)*pw2 0) = 12960
  rw [pw2_0125, pw2_0124, pw2_0001, pw2_0000]
  decide
#print axioms direct_p2_d031_s0_flat40

theorem direct_p2_d031_s1_flat41 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨6,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨6,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 126 - 7^(1+1)*pw2 124) - (pw2 2 - 7^(1+1)*pw2 0) = 65664
  rw [pw2_0126, pw2_0124, pw2_0002, pw2_0000]
  decide
#print axioms direct_p2_d031_s1_flat41

theorem direct_p2_d048_s1_flat42 :
  literalSourceMatrix (1073741824:M) (536870912:M) 7 2 3 5 0 z (pointPosition (⟨2,by decide⟩ : Fin 3)) (colOrder (flatIndex 6 (⟨7,by decide⟩ : Fin 39))) = R747JointBlock39Preflight.A (⟨37,by decide⟩ : Fin 39) (⟨7,by decide⟩ : Fin 39) := by
  rw [literalSourceMatrix_point_entry,z_eq_zFin10]
  unfold sparseObservation
  change (pw2 194 - 7^(1+1)*pw2 192) - (pw2 2 - 7^(1+1)*pw2 0) = 0
  rw [pw2_0194, pw2_0192, pw2_0002, pw2_0000]
  decide
#print axioms direct_p2_d048_s1_flat42

end
end AspisV8R19.R812SourceBlock06P2DirectChunk00
