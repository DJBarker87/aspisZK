import S7Kani3BasisOuter
set_option autoImplicit false
namespace S7Kani3BasisTotal
open Aeneas Aeneas.Std Result
open S7Kani2BasisLoop (Basis basis_block_owned)
open S7Kani3BasisOuter

theorem block_total (basis : Basis) (node : U32) (n j : Usize) (fuel : Nat)
    (hn : n.val ≤ 128) (remaining : j.val+fuel=n.val) :
    ∃ out, basis_block_owned AspisR1Qm31ArithmeticProbe.field.M31.mul basis node n j=ok out := by
  induction fuel generalizing basis j with
  | zero =>
      have stop : j ≥ n := by scalar_tac
      exact ⟨basis,by rw [basis_block_owned]; simp only [stop,if_pos]⟩
  | succ fuel ih =>
      have running : ¬ j ≥ n := by scalar_tac
      obtain ⟨m,hr,_⟩ := WP.spec_imp_exists (Array.index_usize_spec basis j (by simp only [basis.property]; omega))
      obtain ⟨value,hm,_,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod m node
      obtain ⟨i,hi,hiv⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (n.val+j.val) (by scalar_tac)
      have hadd : (n+j : Result Usize)=ok i := hi
      obtain ⟨basis1,hwrite,_⟩ := WP.spec_imp_exists (Array.update_spec basis i value (by simp only [basis.property]; omega))
      obtain ⟨j1,hinc,hj1⟩ := S7Kani2AccumulatorLoop.increment j (by omega)
      obtain ⟨out,hout⟩ := ih basis1 j1 (by omega)
      refine ⟨out,?_⟩
      rw [basis_block_owned]
      simp only [running,if_false,hr,hm,hadd,hwrite,hinc,bind_tc_ok]
      exact hout

/-- Every outer level is total with actual frozen arithmetic. Together with
outer_composition this checks the entire source recurrence at all widths
n*2^fuel≤256, rather than assuming success of each basis block. -/
theorem levels_total (fuel : Nat) (basis : Basis) (node : U32) (n : Usize)
    (hn : 0<n.val) (bound : n.val*2^fuel ≤ 256) :
    ∃ out, levels fuel basis node n=ok out := by
  induction fuel generalizing basis node n with
  | zero => exact ⟨basis,rfl⟩
  | succ fuel ih =>
      have hp : 0<2^fuel := by positivity
      have hm : n.val ≤ n.val*2^fuel := Nat.le_mul_of_pos_right _ hp
      have hs : n.val*2^fuel*2 ≤ 256 := by simpa [pow_succ,Nat.mul_assoc] using bound
      obtain ⟨basis1,hbasis⟩ := block_total basis node n 0#usize n.val (by omega) (by simp)
      obtain ⟨node1,hnode,_⟩ := t2_total node
      obtain ⟨n1,hinc,hn1⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (n.val*2) (by scalar_tac)
      have hmul : (n*2#usize : Result Usize)=ok n1 := hinc
      obtain ⟨out,hout⟩ := ih basis1 node1 n1 (by omega) (by rw [hn1]; simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hs)
      exact ⟨out,by simp only [levels,hbasis,hnode,hmul,bind_tc_ok]; exact hout⟩

theorem production_basis_total (basis : Basis) (node : U32) :
    ∃ out, basis_levels_owned basis node 64#usize 1#usize=ok out := by
  rw [outer_composition basis node 64#usize 1#usize 6 (by decide) (by decide) (by decide)]
  exact levels_total 6 basis node 1#usize (by decide) (by decide)

#print axioms block_total
#print axioms levels_total
#print axioms production_basis_total
end S7Kani3BasisTotal
