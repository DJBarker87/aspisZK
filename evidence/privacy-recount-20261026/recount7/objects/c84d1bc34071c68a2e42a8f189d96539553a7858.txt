import R1Z.PV_Src_ExternalCanonical

/-! One owned source output lane, retaining the exact U64 wrapping addition. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalLaneStep
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open AspisBuilderPoseidonReference
abbrev State := Array U32 16#usize
abbrev Sums := Array U64 4#usize

def cell (s : State) (sums : Sums) (lane : Usize) : U32 :=
  PV_Src_ScalarReduce.value (U64.wrapping_add
    (UScalar.cast .U64 s.val[lane.val]!) sums.val[lane.val%4]!)

theorem canonical (s : State) (sums : Sums) (lane : Usize) :
    (cell s sums lane).val < 2147483647 := PV_Src_ScalarReduce.canonical _

theorem step (s : State) (sums : Sums) (lane : Usize) (hl : lane.val < 16) :
    poseidon2.builder_reference.external_owned_loop2 s sums lane =
      poseidon2.builder_reference.external_owned_loop2 (s.set lane (cell s sums lane))
        sums (Usize.wrapping_add lane 1#usize) := by
  rw [poseidon2.builder_reference.external_owned_loop2,
    if_pos (by simpa [UScalar.lt_equiv] using hl),index_ok s lane (by simpa using hl)]
  simp only [lift,bind_tc_ok]
  rw [rem_ok lane 4#usize (by simp)]
  simp only [bind_tc_ok]
  have hm : (⟨BitVec.umod lane.bv (4#usize : Usize).bv⟩ : Usize).val < 4 := by
    rw [umod_val];exact Nat.mod_lt _ (by decide)
  rw [index_ok_gen sums _ (by simpa using hm)]
  simp only [lift,bind_tc_ok]
  rw [PV_Src_ScalarReduce.reference_eq]
  simp only [bind_tc_ok]
  rw [update_ok _ lane _ (by simpa using hl)]
  simp only [lift,bind_tc_ok,cell,umod_val,UScalar.ofNatCore_val_eq]

#print axioms canonical
#print axioms step
end R1Z.PV_Src_ExternalLaneStep
