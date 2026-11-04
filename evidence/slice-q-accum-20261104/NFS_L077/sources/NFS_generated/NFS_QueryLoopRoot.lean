import NFS_QueryInvariant
import NFP_Resume
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_QueryLoopRoot
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFP_QueryCuts NFG_QueryLoopDefs

def Valid (p : verifier.Prepared) (start finish : Nat) : State → Prop
 | .Err _ => True
 | .Ok (a,b) => NFS_QueryInvariant.Domain p start finish a b

def child (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (qPlace gPlace : Nat) : Query :=
 fun a b => (NFS_QueryValuesPacket.run base proof p a g geometry b qPlace gPlace).result

/-- Every repeated child domain comes from this SAME arbitrary prestate and
its earlier accepted children. Errors, failures, divergence and stop persist. -/
theorem finite (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (qPlace gPlace start : Nat)
 (finish : Usize) (limit : finish.val≤22)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (fuel : Nat) (state : State) (valid : Valid p start finish.val state) :
 run (child base proof p g geometry qPlace gPlace) finish fuel state =
 run (fun a b=>verifier.candidate.query_values (NFS_QueryOps.installed base)
  proof p a g none geometry b) finish fuel state := by
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
     have same := NFS_QueryValuesPacket.result base proof p a g geometry b qPlace gPlace canonical input
     simp only [run,stopped,if_false,child,same]
     cases h : verifier.candidate.query_values (NFS_QueryOps.installed base) proof p a g none geometry b with
     | fail e => rfl
     | div => rfl
     | ok next =>
      simp only [bind_tc_ok]
      apply ih
      cases next with
      | Err error => trivial
      | Ok pair =>
       rcases pair with ⟨after,pending⟩
       exact NFS_QueryInvariant.step base proof p g geometry start finish.val a after b pending valid limit inside h

theorem root (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (qPlace gPlace start : Nat)
 (finish : Usize) (limit : finish.val≤22)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (fuel : Nat) (state : State) (valid : Valid p start finish.val state) (budget : Budget finish fuel state) :
 run (child base proof p g geometry qPlace gPlace) finish fuel state =
 verifier.candidate.query_loop_loop (NFS_QueryOps.installed base) state proof p g none geometry finish :=
 (finite base proof p g geometry qPlace gPlace start finish limit canonical fuel state valid).trans
  (NFG_QueryLoopSource.complete _ _ _ _ _ _ fuel state budget)

theorem tx1 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (domain : NFS_QueryInvariant.Domain p 0 10 a b) (start : a.next.val=0) :
 run (child base proof p g geometry qPlace gPlace) 10#usize 10 (.Ok (a,b)) =
 verifier.candidate.query_loop (NFS_QueryOps.installed base) proof p a g none geometry b 10#usize :=
 (finite base proof p g geometry qPlace gPlace 0 10#usize (by decide) canonical 10 (.Ok (a,b)) domain).trans
  (NFP_Resume.tx1 _ _ _ _ _ _ _ start)

theorem tx2 (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (geometry : verifier.QueryGeometry)
 (b : verifier.BatchedWeights) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (domain : NFS_QueryInvariant.Domain p 10 22 a b) (start : a.next.val=10) :
 run (child base proof p g geometry qPlace gPlace) 22#usize 12 (.Ok (a,b)) =
 verifier.candidate.query_loop (NFS_QueryOps.installed base) proof p a g none geometry b 22#usize :=
 (finite base proof p g geometry qPlace gPlace 10 22#usize (by decide) canonical 12 (.Ok (a,b)) domain).trans
  (NFP_Resume.tx2 _ _ _ _ _ _ _ start)
#print axioms finite
#print axioms root
#print axioms tx1
#print axioms tx2
end AspisR1.NFS_QueryLoopRoot
end
