import NHW_FieldTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_QueryDictionary
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
/-- Explicit deployed primitive installation; remaining callbacks are retained. -/
def model (base : Ops) : Ops :=
 Tx1Q_QueryBridge.leaves {SAQ_Decoder.install base with op20:=FIp_DotsAdapter.dots}
theorem deployed {C : Type} (missing : IDa_Deployed.Uninstalled C) (err : C)
 (r : NP6_StdModel.Reservation) :
 model (NHW_DeployedQuery.configuration missing err r).query=
 Tx1Q_QueryBridge.leaves (NHW_DeployedQuery.configuration missing err r).query := rfl
def prefixRun (ops : Ops) (a : verifier.Accumulator) (node : U32)
 (b : verifier.BatchedWeights) : Result verifier.BatchedWeights := do
 let width:=alloc.vec.Vec.len a.weights
 let zero ← ops.op4
 let one ← ops.op5
 let initial ← Array.update (Array.repeat 256#usize zero) 0#usize one
 let basis ← verifier.accumulate_batched_with_node_loop0 ops one node width initial 1#usize
 verifier.accumulate_batched_with_node_loop1 ops
   {start:=0#usize,«end»:=width} a.weights a.power a.next b width basis
/-- Accumulation's source loops are literally the same before the tail calls. -/
theorem prefix (base : Ops) (a : verifier.Accumulator) (node : U32) (b : verifier.BatchedWeights) :
 prefixRun (model base) a node b=
 prefixRun (NFS_QueryOps.installed (model base)) a node b := rfl

theorem shell (ops : Ops) (p : verifier.Prepared) (a : verifier.Accumulator)
 (node : U32) (value : aspis_core.field.wide_exact.WideExact) (b : verifier.BatchedWeights) :
 verifier.accumulate_batched_with_node ops p a node value b=
 (do
   let mid ← prefixRun ops a node b
   let term ← lift (Usize.wrapping_add mid.terms 1#usize)
   let product ← ops.op3 value a.power
   let rhs ← ops.op2 a.rhs product
   ops.op15 11#u16 a.next rhs
   let power ← ops.op9 a.power p.rho
   let next ← lift (Usize.wrapping_add a.next 1#usize)
   ok ({a with rhs:=rhs,power:=power,next:=next},{mid with terms:=term})) := by
 unfold verifier.accumulate_batched_with_node prefixRun
 simp only [bind_assoc_eq,bind_tc_ok]
 rfl
#print axioms deployed
#print axioms prefix
#print axioms shell
end AspisR1.NHW_QueryDictionary
