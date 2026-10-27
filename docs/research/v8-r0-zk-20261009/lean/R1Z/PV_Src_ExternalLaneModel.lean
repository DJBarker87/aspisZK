import R1Z.PV_Src_ExternalLaneValue

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalLaneModel
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference PV_Src_ExternalLaneStep

theorem total (s : State) (sums : Sums) : ∃ out,
    poseidon2.builder_reference.external_owned_loop2 s sums 0#usize = ok out ∧
    ∀ j : Fin 16, out.val[j.val]! =
      cell s sums (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac)) := by
  refine ⟨PV_Src_ExternalLaneLoop.steps 16 s sums 0#usize,
    PV_Src_ExternalLaneLoop.source 16 s sums 0#usize (by decide),?_⟩
  intro j
  simpa only [UScalar.ofNatCore_val_eq,Nat.not_lt_zero,ite_false] using
    PV_Src_ExternalLaneCells.cells 16 0#usize s sums (by decide) j

theorem model (s : State) (sums : Sums)
    (hs : ∀ j, j < 4 → sums.val[j]!.val < 17179869184)
    {K : Type} [Field K] [CharP K 2147483647] : ∃ out,
    poseidon2.builder_reference.external_owned_loop2 s sums 0#usize = ok out ∧
    (∀ j : Fin 16, out.val[j.val]!.val < 2147483647) ∧
    ∀ j : Fin 16, liftU (K := K) out.val[j.val]! =
      liftU s.val[j.val]!+(sums.val[j.val%4]!.val : K) := by
  obtain ⟨out,ho,hj⟩ := total s sums
  refine ⟨out,ho,?_,?_⟩
  · intro j
    rw [hj j]
    exact PV_Src_ExternalLaneStep.canonical _ _ _
  · intro j
    rw [hj j]
    let lane : Usize := Usize.ofNatCore j.val (by have := j.isLt;scalar_tac)
    have hv : lane.val = j.val := by scalar_tac
    simpa only [hv] using PV_Src_ExternalLaneValue.lift s sums lane
      (by rw [hv];exact hs (j.val%4) (Nat.mod_lt _ (by decide)))


#print axioms total
#print axioms model
end R1Z.PV_Src_ExternalLaneModel
