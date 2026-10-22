import S7JoinProductionBasis

/-! The raw residue caller needs canonical machine words, not just equality
of their reductions. This invariant is derived for the actual emitted basis. -/
set_option autoImplicit false
namespace AspisR1.S7JoinBasisCanonical
open Aeneas Aeneas.Std Result
open AspisCircleGroupOrder
open S7Kani2BasisLoop (Basis)
open S7Kani3BasisOuter
open S7JoinBasisBlock (cell)

def Canonical (b : Basis) : Prop := ∀ j, j<256 → (cell b j).val<P

theorem wordMul_canonical (x y : U32) :
    (S7Kani2PrefixLoop.wordMul x y).val<P := Nat.mod_lt _ (by decide)

theorem block_canonical (b : Basis) (node : U32) (n : Usize)
    (hn : n.val≤128) (hb : Canonical b) :
    ∃ out, S7Kani2BasisLoop.basis_block_owned
      AspisR1Qm31ArithmeticProbe.field.M31.mul b node n 0#usize=ok out ∧ Canonical out := by
  obtain ⟨out,ho,hcells⟩ := S7JoinBasisBlock.block_exact b node n 0#usize n.val hn (by simp)
  refine ⟨out,ho,?_⟩
  intro j hj
  rw [hcells j hj]
  split
  · exact wordMul_canonical _ _
  · exact hb j hj

theorem levels_canonical (fuel : Nat) (b : Basis) (node : U32) (n : Usize)
    (hn : 0<n.val) (bound : n.val*2^fuel≤256) (hb : Canonical b) :
    ∃ out, levels fuel b node n=ok out ∧ Canonical out := by
  induction fuel generalizing b node n with
  | zero => exact ⟨b,rfl,hb⟩
  | succ fuel ih =>
      have hp : 0<2^fuel := by positivity
      have hm : n.val≤n.val*2^fuel := Nat.le_mul_of_pos_right _ hp
      have hs : n.val*2^fuel*2≤256 := by simpa [pow_succ,Nat.mul_assoc] using bound
      obtain ⟨b1,hb1,hcan⟩ := block_canonical b node n (by omega) hb
      obtain ⟨node1,hnode,_⟩ := t2_total node
      obtain ⟨n1,hinc,hn1⟩ := ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (n.val*2) (by scalar_tac)
      have hmul : (n*2#usize : Result Usize)=ok n1 := hinc
      obtain ⟨out,ho,hout⟩ := ih b1 node1 n1 (by omega)
        (by rw [hn1]; simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs) hcan
      exact ⟨out,by simp only [levels,hb1,hnode,hmul,bind_tc_ok]; exact ho,hout⟩

theorem total_canonical (node : U32) : ∃ out,
    S7JoinProductionBasis.basis_owned node=ok out ∧ Canonical out := by
  obtain ⟨b,hb,hset⟩ := WP.spec_imp_exists
    (Array.update_spec (Array.repeat 256#usize 0#u32) 0#usize 1#u32 (by
      change 0<(List.replicate 256 0#u32).length
      rw [List.length_replicate]
      omega))
  have hc : Canonical b := by
    intro j hj
    rw [hset,S7JoinBasisBlock.set_at _ _ _ _ hj]
    split
    · decide
    · change ((List.replicate 256 0#u32)[j]?.getD 0#u32).val<P
      simp only [List.getElem?_replicate,if_pos hj,Option.getD_some]
      decide
  obtain ⟨out,ho,hout⟩ := levels_canonical 6 b node 1#usize (by decide) (by decide) hc
  refine ⟨out,?_,hout⟩
  simp only [S7JoinProductionBasis.basis_owned,hb,bind_tc_ok]
  rw [outer_composition b node 64#usize 1#usize 6 (by decide) (by decide) (by decide)]
  exact ho

/-- Meaning and canonicality together, for every input word. -/
theorem total_exact (node : U32) : ∃ out,
    S7JoinProductionBasis.basis_owned node=ok out ∧ Canonical out ∧
    ∀ j : Fin 64, S7JoinBasisMachine.decode (cell out j.val)=
      AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode node) j.val := by
  obtain ⟨out,ho,hc⟩ := total_canonical node
  obtain ⟨other,hother,hval⟩ := S7JoinProductionBasis.total_exact node
  have he : other=out := Result.ok.inj (hother.symm.trans ho)
  subst other
  exact ⟨out,ho,hc,hval⟩

#print axioms wordMul_canonical
#print axioms block_canonical
#print axioms levels_canonical
#print axioms total_canonical
#print axioms total_exact
end AspisR1.S7JoinBasisCanonical
