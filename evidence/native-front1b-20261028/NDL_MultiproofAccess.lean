import MultiproofConeNodeDomain
import MultiproofConeRootGuard
import NCJ_GuardExact
import NDD_LeafRefs
import NBH_ArrayEq
set_option autoImplicit false
noncomputable section
namespace NDL_MultiproofAccess
open Aeneas Aeneas.Std Result MultiproofConeRef
attribute [local instance] Classical.propDecidable

theorem active_index (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w)
    (active : i.val<s.n.val) : i.val<16 := by
  have hn := domain.2.1
  omega

/-- Native index_at's reference at the actual binary_step input read.
The local index domain follows from the adopted row invariant. -/
theorem index_at (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w)
    (active : i.val<s.n.val) :
    NDD_Reference.index_ref s.idx i =
      ok (NCJ_GuardExact.pick s.idx i.val (active_index physical s i w domain active)) := by
  rw [NDD_LeafRefs.index]
  exact NCJ_GuardExact.index _ _ (active_index physical s i w domain active)

/-- The occupied branch establishes the stricter i+1<16 parent domain from
its REAL i+1<n guard and the SAME row's n<=16 invariant. -/
theorem occupied_domain (physical : Slice U8) (s : reference.Scratch) (i w : Usize)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w)
    (occupied : i.val+1<s.n.val) : i.val+1<16 := by
  have hn := domain.2.1
  omega

/-- The terminal root comparison's exact existing inlined cohort operation,
including all32 bytes, derived from the SAME out.val array. -/
theorem root_matches (s : reference.Scratch) (root : Array U8 32#usize) :
    NDD_Reference.root_ref s.val root =
      ok (decide (NCJ_GuardExact.pick s.val 0 (by decide)=root)) := by
  rw [NDD_LeafRefs.root,NCJ_GuardExact.index _ _ (by decide)]
  simp only [bind_tc_ok,NBH_ArrayEq.source,show (0#usize).val=0 from rfl]

#print axioms active_index
#print axioms index_at
#print axioms occupied_domain
#print axioms root_matches
end NDL_MultiproofAccess
end
