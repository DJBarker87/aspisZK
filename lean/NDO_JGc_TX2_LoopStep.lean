import NDO_JGc_TX2_QueryStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_LoopStep
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

theorem source (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a a1 : verifier.Accumulator) (g : Array SAQ_WideABI.E 29#usize)
    (geometry : verifier.QueryGeometry) (b b1 : verifier.BatchedWeights) (end1 : Usize)
    (active : a.next.val<end1.val)
    (call : verifier.candidate.query_values ops proof p a g none geometry b=ok (.Ok (a1,b1))) :
    verifier.candidate.query_loop ops proof p a g none geometry b end1=
      verifier.candidate.query_loop ops proof p a1 g none geometry b1 end1 := by
  change Port3_NativeQueryBody.verifier.candidate.query_loop_loop ops (.Ok (a,b)) proof p g none geometry end1=_
  rw [Port3_NativeQueryBody.verifier.candidate.query_loop_loop,Aeneas.Std.loop.eq_def]
  simp [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,
    show ¬end1.val≤a.next.val from by omega,call,
    Port3_NativeQueryBody.verifier.candidate.query_loop,
    Port3_NativeQueryBody.verifier.candidate.query_loop_loop]

theorem done (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator) (g : Array SAQ_WideABI.E 29#usize)
    (geometry : verifier.QueryGeometry) (b : verifier.BatchedWeights) (end1 : Usize)
    (atEnd : a.next.val=end1.val) :
    verifier.candidate.query_loop ops proof p a g none geometry b end1=ok (.Ok (a,b)) := by
  change Port3_NativeQueryBody.verifier.candidate.query_loop_loop ops (.Ok (a,b)) proof p g none geometry end1=_
  rw [Port3_NativeQueryBody.verifier.candidate.query_loop_loop,Aeneas.Std.loop.eq_def]
  simp [Port3_NativeQueryBody.verifier.candidate.query_loop_loop.body,atEnd]
#print axioms source
#print axioms done
end AspisR1.JGc_TX2_LoopStep
end
