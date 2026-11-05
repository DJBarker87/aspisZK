import NHW_QueryStep
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
 induction fuel generalizing state with
 | zero => cases state with | Err e=>rfl | Ok pair=>cases pair;rfl
 | succ fuel ih =>
   cases state with
   | Err error => rfl
   | Ok pair =>
     rcases pair with ⟨a,b⟩
     by_cases stopped : a.next≥finish
     · simp only [run,stopped,if_true]
     · have inside : a.next.val<finish.val := Nat.lt_of_not_ge stopped
       have input := NFS_QueryInvariant.active p start finish.val a b valid limit inside
       have same := NHW_QueryStep.source base proof p a g geometry b input
       simp only [run,stopped,if_false,same]
       cases h : verifier.candidate.query_values (NFS_QueryOps.installed (model base)) proof p a g none geometry b with
       | fail e => rfl
       | div => rfl
       | ok next =>
         simp only [bind_tc_ok]
         apply ih
         cases next with
         | Err error => trivial
         | Ok pair =>
           rcases pair with ⟨after,pending⟩
           exact NFS_QueryInvariant.step (model base) proof p g geometry start finish.val a after b pending valid limit inside h

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
