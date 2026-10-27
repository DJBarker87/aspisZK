import XRz_FinishOwned
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_FinishCarrier
open XRx_FinishStep
def emitted (w : S8OwnedP6Finish.Weights) : Slice Q :=
 ⟨w.val.map XRz_FinishValue.newQ,by simpa only [List.length_map] using w.property⟩
/-- Whole finish materialization, lifted from lists to the exact Slice carrier. -/
theorem source (b : verifier.BatchedWeights) (w : Slice Q) (len : w.length≤b.raw.length) :
 verifier.BatchedWeights.finish b w=
 XRo_Join_Carriers.mapR emitted (S8OwnedP6.finish_owned b.raw (XRz_FinishOwned.weights w)) := by
 obtain ⟨out,run,_,_⟩ := XRz_FinishMaterialize.source b w len
 have size : (XRz_FinishOwned.weights w).length=w.length := by
  simp only [XRz_FinishOwned.weights,alloc.vec.Vec.length,List.length_map]
 obtain ⟨owned,hrun,_,_⟩ := S8OwnedP6Finish.finish_total_model b.raw (XRz_FinishOwned.weights w) (by omega)
 have eq := XRz_FinishOwned.source b w len
 rw [run,hrun] at eq
 have listEq := congrArg (List.map XRz_FinishValue.newQ) (Result.ok.inj eq)
 have identity : (out.val.map XRx_ValueOwned.oldQ).map XRz_FinishValue.newQ=out.val := by
  rw [List.map_map]
  change out.val.map id=out.val
  exact congrFun List.map_id_fun out.val
 have listEq' : out.val=owned.val.map XRz_FinishValue.newQ := identity.symm.trans listEq
 have same : out=emitted owned := Subtype.ext listEq'
 rw [run,hrun,same]
 rfl
#print axioms source
end XRz_FinishCarrier
