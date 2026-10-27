import FJm_LibraModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraSparseDot
open scoped BigOperators

theorem value {E : Type} [Field E] (q0 q1 a0 a1 : E) (f : Fin 64 → E) :
    RoundPairing.dot f (FJm_LibraModel.folded q0 q1 a0 a1)=
      ∑ i : Fin 4,f ⟨i.val,by have := i.isLt;omega⟩*FJm_LibraModel.part q0 q1 a0 a1 i := by
  let emb : Fin 4 ↪ Fin 64 := ⟨fun i=>⟨i.val,by have := i.isLt;omega⟩,
    by intro a b h;apply Fin.ext;exact congrArg Fin.val h⟩
  have subset : Finset.univ.map emb ⊆ (Finset.univ : Finset (Fin 64)) := Finset.subset_univ _
  have hsum : (∑ i∈Finset.univ.map emb,f i*FJm_LibraModel.folded q0 q1 a0 a1 i)=
      ∑ i∈(Finset.univ : Finset (Fin 64)),f i*FJm_LibraModel.folded q0 q1 a0 a1 i := by
    apply Finset.sum_subset subset
    intro i _ hi
    have large : 4 ≤ i.val := by
      by_contra h
      have small : i.val<4 := by omega
      apply hi
      exact Finset.mem_map.mpr ⟨⟨i.val,small⟩,Finset.mem_univ _,Fin.ext rfl⟩
    rw [FJm_LibraModel.support q0 q1 a0 a1 i large,mul_zero]
  unfold RoundPairing.dot
  rw [←hsum,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  change f ⟨i.val,by have := i.isLt;omega⟩*
    FJm_LibraModel.folded q0 q1 a0 a1 ⟨i.val,by have := i.isLt;omega⟩=_
  rw [FJm_LibraModel.small q0 q1 a0 a1 i]
#print axioms value
end AspisR1.FJm_LibraSparseDot
end
