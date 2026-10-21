import R1Z.SimulatorR1

/-! The headline allows unbounded public auxiliary output and query keys.
These are size obstructions to a uniform q-only byte-work bound, not a claim
that the protocol's intended fixed encodings are inefficient. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostObstruction
open R0P R0Z.JointView R0Z.RefPayload R1Z.Batched
variable {K CommitHandle : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

theorem simE_public_output (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (x : Statement K CommitHandle) (ch : Challenges K) (t : Tape K F) (n : Nat) :
    ((simE (Bat := R1Bat) π B (fun _ _ => List.replicate n (0 : UInt8)) x ch t).1.publicOutputs).length = n := by
  exact List.length_replicate

/-- No constant query-only bound uniformly over the allowed outputs.
The public output itself can already exceed it, before any oracle query. -/
theorem no_uniform_output_bound (π : Fin 1024 ≃ Fin 1024) (B : PackBasis F)
    (x : Statement K CommitHandle) (ch : Challenges K) (t : Tape K F) (bound : Nat) :
    ∃ outputs : Statement K CommitHandle → Challenges K → List UInt8,
      bound < ((simE (Bat := R1Bat) π B outputs x ch t).1.publicOutputs).length := by
  refine ⟨fun _ _ => List.replicate (bound+1) 0, ?_⟩
  rw [simE_public_output]
  omega

#print axioms simE_public_output
#print axioms no_uniform_output_bound
end R1Z.SimCostObstruction
