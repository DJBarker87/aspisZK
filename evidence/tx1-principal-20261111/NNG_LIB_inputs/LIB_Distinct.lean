import NMX_R2_DistinctPairwise
import NMX_R2_DistinctMap
import NMX_R2_ObserveResult
set_option autoImplicit false
noncomputable section
namespace LIB_Distinct
open Aeneas Aeneas.Std Result AdapterRw NMX_R2_Carrier NGL_DistinctInduction
/-- CLOSED native loop, then symbolic index and carrier association. Both
native outcomes are retained; no successful distinctness premise is a domain. -/
theorem seven (base : Ops) (accounts : Array r1_pool_adapter.owned.OwnedAccount 7#usize)
 (env : RSL.Env) :
 RSL.RS.ofExcept (RSL.requireDistinct (accounts.val.map account)) env
  (NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_distinct_accounts (NGL_ReadonlyModel.install base) accounts)) := by
 rw [NGL_DistinctInduction.source base accounts (by decide)]
 rcases NMX_DistinctValues.reference_values accounts with good | bad
 · have keys := (NMX_R2_DistinctPairwise.success accounts (by decide)).mp good
   have flag := (NMX_R2_DistinctCanonical.success (accounts.val.map account)).mpr
    ((NMX_R2_DistinctMap.pairwise accounts.val).mpr keys)
   rw [good]
   simp only [RSL.requireDistinct,flag,↓reduceIte]
   rfl
 · have flag : RSL.distinctKeys (accounts.val.map account) = false := by
    apply Bool.eq_false_iff.mpr
    intro flag
    have keys := (NMX_R2_DistinctMap.pairwise accounts.val).mp
     ((NMX_R2_DistinctCanonical.success (accounts.val.map account)).mp flag)
    have success := (NMX_R2_DistinctPairwise.success accounts (by decide)).mpr keys
    rw [bad] at success
    cases success
   rw [bad]
   simp only [RSL.requireDistinct,flag,Bool.false_eq_true,↓reduceIte]
   rfl
theorem three (base : Ops) (accounts : Array r1_pool_adapter.owned.OwnedAccount 3#usize)
 (env : RSL.Env) :
 RSL.RS.ofExcept (RSL.requireDistinct (accounts.val.map account)) env
  (NMX_R2_ObserveResult.observe id
   (r1_pool_adapter.owned.require_distinct_accounts (NGL_ReadonlyModel.install base) accounts)) := by
 rw [NGL_DistinctInduction.source base accounts (by decide)]
 rcases NMX_DistinctValues.reference_values accounts with good | bad
 · have keys := (NMX_R2_DistinctPairwise.success accounts (by decide)).mp good
   have flag := (NMX_R2_DistinctCanonical.success (accounts.val.map account)).mpr
    ((NMX_R2_DistinctMap.pairwise accounts.val).mpr keys)
   rw [good]
   simp only [RSL.requireDistinct,flag,↓reduceIte]
   rfl
 · have flag : RSL.distinctKeys (accounts.val.map account) = false := by
    apply Bool.eq_false_iff.mpr
    intro flag
    have keys := (NMX_R2_DistinctMap.pairwise accounts.val).mp
     ((NMX_R2_DistinctCanonical.success (accounts.val.map account)).mp flag)
    have success := (NMX_R2_DistinctPairwise.success accounts (by decide)).mpr keys
    rw [bad] at success
    cases success
   rw [bad]
   simp only [RSL.requireDistinct,flag,Bool.false_eq_true,↓reduceIte]
   rfl
#print axioms seven
#print axioms three
end LIB_Distinct
end
