import NJP_NativeStep
import NJP_CohortNode

set_option autoImplicit false
noncomputable section
namespace NJP_NativeCohortStep
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Native split cuts at their SAME arguments, with the actual child model
installed, transport directly to the cohort's complete node observation.
This is a local native/cohort step, not a whole-verifier row certificate. -/
theorem observation (H : Slice (Slice U8) → RefDigest) (s : reference.Scratch)
    (physical : Slice U8) (i w : Usize) (after : NJP_RowModel.Scratch) (ni nw : Nat)
    (returned : Bool) (log : NJP_NativeRowCut.Log)
    (domain : AspisR1.MultiproofConeNodeDomain.RowDomain physical s i w)
    (active : i.val<s.n.val)
    (cut : NJP_NativeRowCut.Cut (raw s) i.val w.val physical.val.length
      (fun n => physical.val[n]!)
      (NJP_RequestTransport.hash H (NJP_NativeRowCut.request log)) after ni nw returned log) :
 let typed := eval H (AspisR1.MultiproofConePhysicalProgram.node s physical i w)
 (typed.1,mapResult projectRow typed.2)=
 (if log.calls=0 then [] else
    [(NJP_RequestTransport.address (NJP_NativeRowCut.request log),
      H (NJP_RequestTransport.address (NJP_NativeRowCut.request log)))],
  ok (if returned then NJP_RowModel.Row.next after ni nw else NJP_RowModel.Row.stop after)) := by
 dsimp only
 rw [NJP_CohortNode.observation H s physical i w domain active,NJP_RequestTransport.observation]
 rw [NJP_NativeStep.one _ _ _ _ _ _ _ _ _ _ _ cut]
 split <;> simp only [List.map_nil,List.map_cons,NJP_RequestTransport.hash,encode_decode]

#print observation
#print axioms observation
end NJP_NativeCohortStep
end
