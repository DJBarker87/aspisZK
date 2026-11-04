import NFP_TraceTypes
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_TraceHead
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts NFP_TraceTypes
open Port3_NativeQueryBody

def run (base : Ops) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (g : Array E 29#usize) : M (Usize × Slice U8 × Dots) :=
 let ops := NFP_ObserverErasure.erase base
 do
  let i ← eval (Array.index_usize p.queries a.next)
  let u ← eval (lift (UScalar.cast .Usize i))
  mark (.opening proof a.next)
  let q ← eval (ops.op11 proof a.next)
  mark (.dots q g)
  let dots ← eval (ops.op20 q g)
  pure (u,q,dots)

theorem erased (base : Ops) (proof : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator) (g : Array E 29#usize) :
 (run base proof p a g).result = NFP_QueryCuts.head (NFP_ObserverErasure.erase base) proof p a g := by
 simp only [run,eval,mark,NFI_TraceResult.erase_bind,NFI_TraceResult.erase_lift,
  NFI_TraceResult.erase_mark,pure_result,bind_tc_ok,
  NFP_QueryCuts.head,NFP_SuffixCuts.front,NFP_SuffixCuts.back] <;> rfl
#print axioms erased
end AspisR1.NFP_TraceHead
end
