import NFS_QueryLoopRoot
import NFP_QueryTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_LoopTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody NFP_QueryCuts NFP_TraceTypes NFG_QueryLoopDefs

def run (query : verifier.Accumulator → verifier.BatchedWeights → M State) (finish : Usize) : Nat → State → M State
 | 0,state => match state with
   | .Err _ => pure state
   | .Ok (a,_) => if a.next≥finish then pure state else eval div
 | fuel+1,state => match state with
   | .Err _ => pure state
   | .Ok (a,b) => if a.next≥finish then pure state else do
      let next ← query a b
      run query finish fuel next

theorem bind_congr {A B : Type} (before : M A) (first second : A → M B)
 (same : ∀ a,before.result=ok a → first a=second a) :
 (before >>= first)=(before >>= second) := by
 rcases before with ⟨r,cuts⟩
 cases r with
 | fail e => rfl
 | div => rfl
 | ok a => exact congrArg (fun after : M B=>NFI_TraceResult.M.mk after.result (cuts++after.cuts)) (same a rfl)

theorem source (base : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (g : Array E 29#usize) (geometry : verifier.QueryGeometry) (qPlace gPlace start : Nat)
 (finish : Usize) (limit : finish.val≤22)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g))
 (fuel : Nat) (state : State) (valid : NFS_QueryLoopRoot.Valid p start finish.val state) :
 run (fun a b=>NFS_QueryValuesPacket.run base proof p a g geometry b qPlace gPlace) finish fuel state =
 run (fun a b=>NFP_QueryTrace.run (NFS_QueryOps.installed base) proof p a g geometry b) finish fuel state := by
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
     have same := NFS_QueryValuesPacket.source base proof p a g geometry b qPlace gPlace canonical input
     simp only [run,stopped,if_false,same]
     apply bind_congr
     intro next h
     apply ih
     have actual : verifier.candidate.query_values (NFS_QueryOps.installed base) proof p a g none geometry b=ok next := by
      simpa only [NFP_QueryTrace.erased] using h
     cases next with
     | Err error => trivial
     | Ok pair =>
      rcases pair with ⟨after,pending⟩
      exact NFS_QueryInvariant.step base proof p g geometry start finish.val a after b pending valid limit inside actual

/-- Erasing observations recovers the existing partial-Result induction;
failed/divergent prefixes retain their accumulated observations in run. -/
theorem erased (query : verifier.Accumulator → verifier.BatchedWeights → M State)
 (finish : Usize) (fuel : Nat) (state : State) :
 (run query finish fuel state).result = NFG_QueryLoopDefs.run (fun a b=>(query a b).result) finish fuel state := by
 induction fuel generalizing state with
 | zero => cases state with | Err e=>rfl | Ok pair=>cases pair;rfl
 | succ fuel ih =>
  cases state with
  | Err error => rfl
  | Ok pair =>
   rcases pair with ⟨a,b⟩
   by_cases stopped : a.next≥finish
   · simp only [run,NFG_QueryLoopDefs.run,stopped,if_true,pure_result]
   · simp only [run,NFG_QueryLoopDefs.run,stopped,if_false,NFI_TraceResult.erase_bind,ih]
#print axioms bind_congr
#print axioms source
#print axioms erased
end AspisR1.NFS_LoopTrace
end
