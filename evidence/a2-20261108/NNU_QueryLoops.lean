import NNH_Run5bQuerySlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryLoops
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

structure Slots (g h : Ops) : Prop where
 embed : g.op1=h.op1
 zero : g.op4=h.op4
 one : g.op5=h.op5
 sub : g.op6=h.op6
 mul : g.op7=h.op7
 double : g.op8=h.op8
 embedM : g.op10=h.op10
 read : g.op12=h.op12
 basis : g.op13=h.op13
 push : g.op14=h.op14
 trace : g.op15=h.op15

theorem innerStep (g h : Ops) (s : Slots g h) (node : U32) (n : Usize)
 (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize) :
 verifier.accumulate_batched_with_node_loop0_loop0.body g node n iter basis =
 verifier.accumulate_batched_with_node_loop0_loop0.body h node n iter basis := by
 simp only [verifier.accumulate_batched_with_node_loop0_loop0.body,s.mul]

theorem innerLoop (g h : Ops) (s : Slots g h) (node : U32) (n : Usize)
 (iter : core.ops.range.Range Usize) (basis : Array U32 256#usize) :
 verifier.accumulate_batched_with_node_loop0_loop0 g iter node basis n =
 verifier.accumulate_batched_with_node_loop0_loop0 h iter node basis n := by
 unfold verifier.accumulate_batched_with_node_loop0_loop0
 apply congrArg (fun f=>Aeneas.Std.loop f (iter,basis))
 funext state
 exact innerStep g h s node n state.1 state.2

theorem basisStep (g h : Ops) (s : Slots g h) (m node : U32) (width n : Usize)
 (basis : Array U32 256#usize) :
 verifier.accumulate_batched_with_node_loop0.body g m width node basis n =
 verifier.accumulate_batched_with_node_loop0.body h m width node basis n := by
 simp only [verifier.accumulate_batched_with_node_loop0.body,innerLoop g h s,s.mul,s.double,s.sub]

theorem basisLoop (g h : Ops) (s : Slots g h) (m node : U32) (width n : Usize)
 (basis : Array U32 256#usize) :
 verifier.accumulate_batched_with_node_loop0 g m node width basis n =
 verifier.accumulate_batched_with_node_loop0 h m node width basis n := by
 unfold verifier.accumulate_batched_with_node_loop0
 apply congrArg (fun f=>Aeneas.Std.loop f (node,basis,n))
 funext state
 exact basisStep g h s m state.1 width state.2.2 state.2.1

theorem rowStep (g h : Ops) (s : Slots g h) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (i width : Usize) (basis : Array U32 256#usize)
 (iter : core.ops.range.Range Usize) (b : verifier.BatchedWeights) :
 verifier.accumulate_batched_with_node_loop1.body g v q i width basis iter b =
 verifier.accumulate_batched_with_node_loop1.body h v q i width basis iter b := by
 simp only [verifier.accumulate_batched_with_node_loop1.body,s.basis,s.push,s.read,s.embed,s.trace,s.embedM]

theorem rowLoop (g h : Ops) (s : Slots g h) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (i width : Usize) (basis : Array U32 256#usize)
 (iter : core.ops.range.Range Usize) (b : verifier.BatchedWeights) :
 verifier.accumulate_batched_with_node_loop1 g iter v q i b width basis =
 verifier.accumulate_batched_with_node_loop1 h iter v q i b width basis := by
 unfold verifier.accumulate_batched_with_node_loop1
 apply congrArg (fun f=>Aeneas.Std.loop f (iter,b))
 funext state
 exact rowStep g h s v q i width basis state.1 state.2
#print axioms innerStep
#print axioms innerLoop
#print axioms basisStep
#print axioms basisLoop
#print axioms rowStep
#print axioms rowLoop
end AspisR1.NNU_QueryLoops
end
