import Lean
import NFN_PhaseTransport
import NFS_NEV_AccumulateRaw_Funs
import NBF_Accumulate

set_option autoImplicit false
noncomputable section
namespace NFS_NEV_AccumulateTail
open Aeneas Aeneas.Std Result NEV_AccumulateRaw
/-- Exact newly emitted prefix, not a successful-loop assumption. -/
def rows (a : Accumulator) (node : U32) (weights : BatchedWeights) : Result BatchedWeights := do
 let width := alloc.vec.Vec.len a.weights
 let zero ← aspis_core.field.M31.ZERO
 let one ← aspis_core.field.M31.ONE
 let initialized ← Array.update (Array.repeat 256#usize zero) 0#usize one
 let basis ← accumulate_batched_with_node_loop0 one node width initialized 1#usize
 accumulate_batched_with_node_loop1 {start:=0#usize,«end»:=width}
   a.weights a.power a.next weights width basis
/-- Exact checked counter updates and concrete lower field callees. -/
def tail (p : Prepared) (a : Accumulator)
    (value : aspis_core.field.wide_exact.WideExact) (weights : BatchedWeights) :
    Result (Accumulator × BatchedWeights) := do
 let terms ← weights.terms+1#usize
 let product ← aspis_core.field.wide_exact.WideExact.mul_qm31 value a.power
 let rhs ← aspis_core.field.wide_exact.WideExact.add a.rhs product
 trace.value 11#u16 a.next rhs
 let power ← aspis_core.field.QM31.mul a.power p.rho
 let next ← a.next+1#usize
 ok ({a with rhs:=rhs,power:=power,next:=next},{weights with terms:=terms})

/-- Full Result decomposition: failed/divergent prefix or field call is kept,
including the original order of both independent counter operations. -/
theorem source_cut (p : Prepared) (a : Accumulator) (node : U32)
    (value : aspis_core.field.wide_exact.WideExact) (weights : BatchedWeights) :
    accumulate_batched_with_node p a node value weights =
      (do let middle ← rows a node weights;tail p a value middle) := by
  unfold accumulate_batched_with_node rows tail
  simp only [bind_assoc_eq,bind_tc_ok]

/-- The tail returns exactly the SAME vectors. This is a model carrier frame;
the native mutable/physical frame is separately checked by K036/K037. -/
theorem successful_frame (p : Prepared) (a out : Accumulator)
    (value : aspis_core.field.wide_exact.WideExact) (middle result : BatchedWeights)
    (run : tail p a value middle=ok (out,result)) :
    out.weights=a.weights ∧ result.raw=middle.raw := by
  unfold tail at run
  iterate 6 obtain ⟨x,hx,run⟩ := AspisR1.Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  exact ⟨rfl,rfl⟩

#print axioms source_cut
#print axioms successful_frame
end NFS_NEV_AccumulateTail
end

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
