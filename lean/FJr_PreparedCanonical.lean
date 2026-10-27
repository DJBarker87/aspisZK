import FJr_SourceCanonical
import FJr_CircleOuterCell
import FJr_AlphaPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_PreparedCanonical
open Aeneas Aeneas.Std Result
open AspisR1Stage2
open CheckpointBytes4ReaderFields

theorem value (p : verifier.Prepared) (a : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (fields : CheckpointBytes4SavedFields.BodyMatches p a pm am) :
    FJc_WeightArray.canonical (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ p.semantic_alpha) ∧
    FJr_CircleOuterCell.CanonZ (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint p.z) ∧
    (∀ x∈p.alpha.val,FIo_WideValues.Canon (FIo_Install.toE x)) ∧
    FIo_WideValues.Canon (FIo_Install.toE p.kappa) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro q hq
    change q∈p.semantic_alpha.val.map FIn_WeightsInstall.toQ at hq
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hq
    rw [fields.semantic] at hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact FJr_SourceCanonical.k x
  · have kc (q : aspis_core.field.QM31) (mem : q∈p.z.val.flatMap (fun z=>[z.x,z.y])) :
        FJg_ReaderScalarCanon.CanonK q := by
      rw [fields.coordinates] at mem
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp mem
      exact FJr_SourceCanonical.k x
    intro point hp
    change point∈p.z.val.map FIn_WeightsInstall.toPoint at hp
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hp
    exact ⟨kc z.x (List.mem_flatMap.mpr ⟨z,hz,by simp⟩),kc z.y (List.mem_flatMap.mpr ⟨z,hz,by simp⟩)⟩
  · intro x hx
    rw [fields.alpha] at hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl
    · exact FJr_SourceCanonical.e (pm.alpha 0)
    · exact FJr_SourceCanonical.e (pm.alpha 1)
  · rw [fields.kappa]
    exact FJr_SourceCanonical.e pm.kappa

#print axioms value
end AspisR1.FJr_PreparedCanonical
end
