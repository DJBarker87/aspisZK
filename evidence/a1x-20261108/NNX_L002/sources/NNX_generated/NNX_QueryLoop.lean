import NNU_QueryInduction
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNX_QueryLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFG_QueryLoopDefs
/-- Dictionary-parametric query transport. All Result arms are preserved;
only reached pre-states require a pointwise child law. -/
theorem generic (ops : Ops) (base : Ops)
 (proof : Slice U8) (p : verifier.Prepared)
 (g : Array aspis_core.field.wide_exact.WideExact 29#usize) (geo : verifier.QueryGeometry)
 (start : Nat) (finish : Usize) (limit : finish.val ≤ 22)
 (same : ∀ a b, NFS_QueryInvariant.Domain p start finish.val a b →
  verifier.candidate.query_values ops proof p a g none geo b =
  verifier.candidate.query_values (NFS_QueryOps.installed base) proof p a g none geo b)
 (fuel : Nat) (state : State) (valid : NFS_QueryLoopRoot.Valid p start finish.val state) :
 run (fun a b => verifier.candidate.query_values ops proof p a g none geo b) finish fuel state =
 run (fun a b => verifier.candidate.query_values (NFS_QueryOps.installed base) proof p a g none geo b) finish fuel state := by
 apply NNU_QueryInduction.finite _ _ (NFS_QueryLoopRoot.Valid p start finish.val) finish
 · exact same
 · intro a b after pending domain inside step
   exact NFS_QueryInvariant.step base proof p g geo start finish.val
    a after b pending domain limit inside step
 · exact valid

theorem tx1 (ops base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (geo : verifier.QueryGeometry) (b : verifier.BatchedWeights)
 (same : ∀ a b, NFS_QueryInvariant.Domain p 0 10 a b →
  verifier.candidate.query_values ops proof p a g none geo b =
  verifier.candidate.query_values (NFS_QueryOps.installed base) proof p a g none geo b)
 (domain : NFS_QueryInvariant.Domain p 0 10 a b) (start : a.next.val=0) :
 verifier.candidate.query_loop ops proof p a g none geo b 10#usize =
 verifier.candidate.query_loop (NFS_QueryOps.installed base) proof p a g none geo b 10#usize :=
 (NFP_Resume.tx1 _ _ _ _ _ _ _ start).symm.trans
  ((generic ops base proof p g geo 0 10#usize (by decide) same 10 (.Ok (a,b)) domain).trans
   (NFP_Resume.tx1 _ _ _ _ _ _ _ start))
#print axioms generic
#print axioms tx1
end AspisR1.NNX_QueryLoop
end
