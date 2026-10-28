import NBO_AllCalls
set_option autoImplicit false
namespace NBO_WeightRead
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
/-- The SAME reached weight read supplies the embedding's canonical domain.
No selected success or canonical output is independently supplied. -/
theorem read (weights : alloc.vec.Vec NBF_RowInstall.Q)
 (canonical : NBO_AllCalls.CanonicalWeights weights) (j : Usize)
 (bound : j.val<weights.val.length) :
 ∃ q, core.slice.index.Slice.index (core.slice.index.SliceIndexUsizeSlice NBF_RowInstall.Q)
   weights.deref j=ok q ∧ NBF_PowerStep.Canonical q := by
 obtain ⟨q,run,contents⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec weights j bound)
 refine ⟨q,run,?_⟩
 rw [contents]
 exact canonical _ (List.getElem_mem _)
/-- Literal wide embedding is canonical on exactly the derived Q domain. -/
theorem embed (q : NBF_RowInstall.Q) (canonical : NBF_PowerStep.Canonical q) :
 NBO_TailDomain.WideCanonical (NBF_RowInstall.embedQ q) := by
 refine ⟨canonical,?_⟩
 intro k
 fin_cases k <;> decide
#print axioms read
#print axioms embed
end NBO_WeightRead
