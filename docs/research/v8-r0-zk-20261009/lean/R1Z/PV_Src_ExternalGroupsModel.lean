import R1Z.PV_Src_ExternalGroupsCopy

set_option autoImplicit false
namespace R1Z.PV_Src_ExternalGroupsModel
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open AspisBuilderPoseidonReference PV_Src_ExternalBlockStep

theorem source (s : State) {K : Type} [Field K] [CharP K 2147483647] :
    ∃ gr, poseidon2.builder_reference.external_owned_loop0 s 0#usize = ok gr ∧
      ∀ (g c : Nat) (hg : g < 4) (hc : c < 4),
        liftU (K := K) gr.val[4*g+c]! = PM s ⟨g,hg⟩ ⟨c,hc⟩ := by
  obtain ⟨gr,hgr,hG,_⟩ := groups_loop (K := K) s 4 0#usize
    (Array.repeat 16#usize 0#u32) (by decide)
  refine ⟨gr,?_,?_⟩
  · rw [PV_Src_ExternalGroupsCopy.source,R0PoseidonCopy.ext_groups]
    exact hgr
  · intro g c hg hc
    exact hG g c hg hc (by simp)

#print axioms source
end R1Z.PV_Src_ExternalGroupsModel
