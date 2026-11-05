import NHW_QueryStep
import NHW_LoopCongruence
import NHW_DeployedStabilize
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_QueryLoop
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
open NFP_QueryCuts NFG_QueryLoopDefs NHW_QueryDictionary
/-- One arbitrary query step, followed by finite induction on the existing
loop invariant. Errors/fail/divergence retain their actual prefix. -/
theorem finite (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (start : Nat)
 (finish : Usize) (limit : finish.val≤22) (fuel : Nat) (state : State)
 (valid : NFS_QueryLoopRoot.Valid p start finish.val state) :
 run (fun a b=>verifier.candidate.query_values (model base) proof p a g none geometry b) finish fuel state=
 run (fun a b=>verifier.candidate.query_values (NFS_QueryOps.installed (model base)) proof p a g none geometry b) finish fuel state := by
 apply NHW_LoopCongruence.source
 · intro a b domain inside
   exact NHW_QueryStep.source base proof p a g geometry b
     (NFS_QueryInvariant.active p start finish.val a b domain limit inside)
 · intro a b after pending domain inside h
   exact NFS_QueryInvariant.step (model base) proof p g geometry start finish.val a after b pending domain limit inside h
 · exact valid

theorem tx1 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (domain : NFS_QueryInvariant.Domain p 0 10 a b)
 (start : a.next.val=0) :
 verifier.candidate.query_loop (model base) proof p a g none geometry b 10#usize=
 verifier.candidate.query_loop (NFS_QueryOps.installed (model base)) proof p a g none geometry b 10#usize :=
 (NFP_Resume.tx1 (model base) proof p a g geometry b start).symm.trans
   ((finite base proof p g geometry 0 10#usize (by decide) 10 (.Ok (a,b)) domain).trans
     (NFP_Resume.tx1 (NFS_QueryOps.installed (model base)) proof p a g geometry b start))
#print axioms finite
#print axioms tx1
end AspisR1.NHW_QueryLoop
