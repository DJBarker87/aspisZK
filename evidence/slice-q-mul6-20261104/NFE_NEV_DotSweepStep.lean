import NFE_NEV_DotSweep
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NFE_NEV_DotSweepStep
open Aeneas Aeneas.Std Result
/-- A successful actual cell and its full disjoint-word invariant are DERIVED
from the reached pre-state, not supplied as a caller/callee success premise. -/
theorem step (n : Nat) (active : n<4) (index : Usize) (inside : index.val<8)
    (coefficient : Array U32 8#usize) (canonical : ∀ word∈coefficient.val,word.val<NEG_DotDomain.P)
    (scalar : U32) (scalarCanonical : scalar.val<NEG_DotDomain.P)
    (sums : Array U64 8#usize) (invariant : NFE_NEV_DotSweep.Sweep n index.val sums) :
    ∃ out,NFE_NEV_DotCell.cell coefficient scalar sums index=ok out ∧
      NFE_NEV_DotSweep.Sweep n (index.val+1) out := by
  obtain ⟨word,readWord,wordAt⟩:=WP.spec_imp_exists
    (Array.index_usize_spec coefficient index (by change index.val<coefficient.val.length;rw [coefficient.property];exact inside))
  have wordCanonical : word.val<NEG_DotDomain.P := by
    apply canonical word
    rw [wordAt]
    exact List.getElem_mem _
  obtain ⟨before,readSum,_⟩:=WP.spec_imp_exists
    (Array.index_usize_spec sums index (by change index.val<sums.val.length;rw [sums.property];exact inside))
  have bound:=NFE_NEV_DotSweep.current n index inside sums invariant before readSum
  obtain ⟨after,run,value,boundAfter⟩:=NFE_NEV_DotCell.total coefficient scalar word sums index before n
    inside readWord readSum wordCanonical scalarCanonical active bound
  exact ⟨sums.set index after,run,NFE_NEV_DotSweep.write n index inside sums after invariant boundAfter⟩
/-- Finishing one term supplies the next term's pre-state, on the SAME array. -/
theorem next_term (n : Nat) (sums : Array U64 8#usize)
    (invariant : NFE_NEV_DotSweep.Sweep n 8 sums) : NFE_NEV_DotSweep.Sweep (n+1) 0 sums := by
  intro i
  have bound:=invariant i
  simpa only [if_pos i.isLt,Nat.not_lt_zero,if_false] using bound
#print axioms step
#print axioms next_term
end NFE_NEV_DotSweepStep
end
