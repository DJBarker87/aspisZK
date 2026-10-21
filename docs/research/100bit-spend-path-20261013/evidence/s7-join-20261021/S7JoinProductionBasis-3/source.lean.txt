import S7JoinBasisMachine
set_option autoImplicit false
namespace AspisR1.S7JoinProductionBasis
open Aeneas Aeneas.Std Result
open S7Kani2BasisLoop (Basis)
open S7JoinBasisMachine
open AspisCircleGroupOrder AspisCircleTensorBinding

def basis_owned (node : U32) : Result Basis := do
  let b ← Array.update (Array.repeat 256#usize 0#u32) 0#usize 1#u32
  S7Kani3BasisOuter.basis_levels_owned b node 64#usize 1#usize

/-- Entire concrete emitted initialization, blocks and outer schedule. -/
theorem total_exact (node : U32) : ∃ out,
    basis_owned node=ok out ∧ ∀ j : Fin 64,
      decode (S7JoinBasisBlock.cell out j.val)=naturalLineValue (decode node) j.val := by
  obtain ⟨b,hb,hset⟩ := WP.spec_imp_exists
    (Array.update_spec (Array.repeat 256#usize 0#u32) 0#usize 1#u32 (by
      change 0 < (List.replicate 256 0#u32).length
      rw [List.length_replicate]
      omega))
  have hprefix : Prefix b (decode node) 1 := by
    intro j hj
    have hj0 : j=0 := by omega
    subst j
    rw [hset,S7JoinBasisBlock.set_at _ _ _ _ (by decide)]
    simp only [show (0#usize).val=0 from rfl,if_pos rfl,decode,
      show (1#u32).val=1 from rfl,Nat.cast_one,naturalLineValue,
      Nat.bitIndices_zero,List.toFinset_nil,Finset.prod_empty]
  obtain ⟨out,ho,hpre⟩ := levels_prefix 6 0 (decode node) b node 1#usize
    (by rfl) (by decide) hprefix (by rfl)
  refine ⟨out,?_,fun j => hpre j.val j.isLt⟩
  simp only [basis_owned,hb,bind_tc_ok]
  rw [S7Kani3BasisOuter.outer_composition b node 64#usize 1#usize 6
    (by decide) (by decide) (by decide)]
  exact ho

#print axioms total_exact
end AspisR1.S7JoinProductionBasis
