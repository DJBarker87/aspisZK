import NFE_NEV_DotCell
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFE_NEV_DotSweep
open Aeneas Aeneas.Std Result
/-- Each word before cursor has one more product; remaining words retain n.
This disjoint-word invariant is over the SAME owned array, not eight oracles. -/
def Sweep (n cursor : Nat) (sums : Array U64 8#usize) : Prop :=
 ∀ i : Fin 8,(sums.val[i.val]'(by rw [sums.property];exact i.isLt)).val≤
   (if i.val<cursor then (n+1)*NEG_DotDomain.B else n*NEG_DotDomain.B)

theorem write (n : Nat) (index : Usize) (inside : index.val<8)
    (sums : Array U64 8#usize) (after : U64) (invariant : Sweep n index.val sums)
    (bound : after.val≤(n+1)*NEG_DotDomain.B) :
    Sweep n (index.val+1) (sums.set index after) := by
  intro i
  change ((sums.val.set index.val after)[i.val]'_).val≤_
  simp only [List.getElem_set]
  by_cases equal : index.val=i.val
  · simp only [if_pos equal]
    have done : i.val < index.val+1 := by omega
    simpa only [if_pos done] using bound
  · simp only [if_neg equal]
    have old:=invariant i
    by_cases order : i.val < index.val
    · have done : i.val < index.val+1 := by omega
      simpa only [if_pos order,if_pos done] using old
    · have pending : ¬i.val < index.val+1 := by omega
      simpa only [if_neg order,if_neg pending] using old

theorem current (n : Nat) (index : Usize) (inside : index.val<8)
    (sums : Array U64 8#usize) (invariant : Sweep n index.val sums)
    (word : U64) (run : Array.index_usize sums index=ok word) :
    word.val≤n*NEG_DotDomain.B := by
  obtain ⟨actual,actualRun,point⟩:=WP.spec_imp_exists
    (Array.index_usize_spec sums index (by change index.val<sums.val.length;rw [sums.property];exact inside))
  have same : actual=word := Result.ok.inj (actualRun.symm.trans run)
  have equality : word=sums.val[index.val]'(by rw [sums.property];exact inside):=same.symm.trans point
  rw [equality]
  have bound:=invariant ⟨index.val,inside⟩
  simpa only [Nat.lt_irrefl,if_false] using bound

theorem native_domain (n : Nat) (active : n<4) (index : Usize) (inside : index.val<8)
    (sums : Array U64 8#usize) (invariant : Sweep n index.val sums)
    (word : U64) (run : Array.index_usize sums index=ok word) :
    word.val≤13835058029512359948 := by
  have bound:=current n index inside sums invariant word run
  have cap:=Nat.mul_le_mul_right NEG_DotDomain.B (show n≤3 by omega)
  norm_num [NEG_DotDomain.B] at bound cap
  omega
#print axioms write
#print axioms current
#print axioms native_domain
end NFE_NEV_DotSweep
end
