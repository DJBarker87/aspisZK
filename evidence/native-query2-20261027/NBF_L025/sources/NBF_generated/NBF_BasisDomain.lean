import NBF_BasisOuter
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_BasisDomain
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- The literal direct native initialization and six-level basis producer. -/
def source (ops : Ops) (node : U32) : Result (Array U32 256#usize) := do
 let b ← Array.update (Array.repeat 256#usize 0#u32) 0#usize 1#u32
 verifier.accumulate_batched_with_node_loop0 (NBF_BasisInstall.install ops)
   1#u32 node 64#usize b 1#usize

theorem association (ops : Ops) (node : U32) :
 source ops node=S7JoinProductionBasis.basis_owned node := by
 unfold source S7JoinProductionBasis.basis_owned
 congr 1
 funext b
 rw [NBF_BasisOuter.levels_eq ops 6 b node 1#usize 64#usize (by decide) (by decide) (by decide)]
 rw [S7Kani3BasisOuter.outer_composition b node 64#usize 1#usize 6 (by decide) (by decide) (by decide)]

theorem total (ops : Ops) (node : U32) :
 ∃ basis, source ops node=ok basis ∧ S7JoinBasisCanonical.Canonical basis := by
 rw [association]
 exact S7JoinBasisCanonical.total_canonical node

/-- SAME returned basis supplies every reached row's canonical scalar domain. -/
theorem read_canonical (ops : Ops) (node : U32) (basis : Array U32 256#usize)
 (run : source ops node=ok basis) (j : Usize) (bound : j.val<256)
 (m : U32) (read : Array.index_usize basis j=ok m) : m.val<2^31-1 := by
 obtain ⟨actual,ha,hc⟩ := total ops node
 have same := Result.ok.inj (ha.symm.trans run)
 subst actual
 have len : j.val<basis.val.length := by rw [basis.property];exact bound
 obtain ⟨value,hvalue,atIndex⟩ := WP.spec_imp_exists (Array.index_usize_spec basis j len)
 have eq : value=m := Result.ok.inj (hvalue.symm.trans read)
 have canonical := hc j.val bound
 have cell : S7JoinBasisBlock.cell basis j.val=m := by
   simp only [S7JoinBasisBlock.cell,List.getElem?_eq_getElem len,Option.getD_some]
   exact atIndex.symm.trans eq
 rw [cell] at canonical
 exact canonical
#print axioms association
#print axioms total
#print axioms read_canonical
end NBF_BasisDomain
