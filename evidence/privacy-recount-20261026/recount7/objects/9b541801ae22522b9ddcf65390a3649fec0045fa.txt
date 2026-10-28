import R1Z.PV_Src_ExternalReference
import R1Z.PV_Src_Forest_DigestTotal

/-! Symbolic totality of the pure external-layer scalar and matrix callees.
No concrete permutation is reduced. -/
set_option autoImplicit false
namespace R1Z.PV_Src_ExternalReduce
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderPoseidonReference
open PV_Src_Forest_DigestTotal

theorem reduce_total (x : U64) : ∃ z, aspis_core.field.M31.reduce_u62 x = ok z := by
  rw [aspis_core.field.M31.reduce_u62,aspis_core.field.reduce_u64]
  simp only [lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem mat4_total (x : Array U32 4#usize) :
    ∃ y, poseidon2.builder_reference.mat4_owned x = ok y := by
  rw [poseidon2.builder_reference.mat4_owned,index_ok x 0#usize (by decide)]
  simp only [lift,bind_tc_ok]
  rw [index_ok x 1#usize (by decide)]
  simp only [lift,bind_tc_ok]
  rw [index_ok x 2#usize (by decide)]
  simp only [lift,bind_tc_ok]
  rw [index_ok x 3#usize (by decide)]
  try simp only [lift,bind_tc_ok]
  apply bind_total _ _ (reduce_total _)
  intro a
  try simp only [lift,bind_tc_ok]
  apply bind_total _ _ (reduce_total _)
  intro b
  try simp only [lift,bind_tc_ok]
  apply bind_total _ _ (reduce_total _)
  intro c
  try simp only [lift,bind_tc_ok]
  apply bind_total _ _ (reduce_total _)
  intro d
  exact ⟨_,rfl⟩

#print axioms reduce_total
#print axioms mat4_total
end R1Z.PV_Src_ExternalReduce
