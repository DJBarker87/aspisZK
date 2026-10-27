import R1Z.PV_Src_ExternalSumValue

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalSumModel
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference PV_Src_ExternalSumStep

theorem total (s : State) : ∃ sums,
    poseidon2.builder_reference.external_owned_loop1 s (Array.repeat 4#usize 0#u64)
      0#usize = ok sums ∧
    ∀ j : Fin 4, sums.val[j.val]! =
      cell s (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac)) := by
  refine ⟨PV_Src_ExternalSumLoop.steps 4 s (Array.repeat 4#usize 0#u64) 0#usize,
    PV_Src_ExternalSumLoop.source 4 s _ 0#usize (by decide),?_⟩
  intro j
  simpa only [UScalar.ofNatCore_val_eq,Nat.not_lt_zero,ite_false] using
    PV_Src_ExternalSumCells.cells 4 s (Array.repeat 4#usize 0#u64) 0#usize (by decide) j

theorem bound (s : State) (sums : Sums)
    (hs : ∀ j : Fin 4, sums.val[j.val]! =
      cell s (Usize.ofNatCore j.val (by have := j.isLt;scalar_tac))) :
    ∀ j, j < 4 → sums.val[j]!.val < 17179869184 := by
  intro j hj
  rw [hs ⟨j,hj⟩]
  exact PV_Src_ExternalSumValue.bound s _

#print axioms total
#print axioms bound
end R1Z.PV_Src_ExternalSumModel
