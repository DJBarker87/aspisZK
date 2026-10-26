import ARU_AllWorld
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_Fresh
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem address (logs : List Bytes) : ∃ b : Bytes, b ∉ logs := by
  classical
  let n := logs.toFinset.sup List.length
  refine ⟨List.replicate (n+1) 0,?_⟩
  intro member
  have bound : (List.replicate (n+1) (0 : Fin 256)).length ≤ n :=
    Finset.le_sup (f := List.length) (List.mem_toFinset.mpr member)
  simp only [List.length_replicate] at bound
  omega

#print axioms address
end AspisR1.ARV_Fresh
end
