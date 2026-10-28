import NDO_JGs_LibraProgram
import NDO_JGs_LibraStage0
import NDO_JGs_LibraStage1
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGs_LibraForward
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE NQ)
open FJm_LibraStages (Weights)
/-- Forward composition under symbolic native inputs; actual instantiation must
supply every primitive stage on the same operand tuple. -/
theorem source (ap0 ap1 : Weights) (extra : Array NQ 2#usize)
    (iter cursor : FIo_RangeNext.Range) (before after : Weights) (side : Usize)
    (base high : Array NQ 4#usize) (q4 q16 : NQ) (low : NE)
    (i0 i1 i2 i3 : Usize) (t0 t1 t2 t3 first2 first3 all : NE)
    (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=ok (some side,cursor))
    (powers : FJm_LibraStages.powers extra side=ok (base,high,q4,q16))
    (scalar : FIo_Native.weights.Weights.scalar_factor base ap0=ok low)
    (term0 : FJm_LibraStages.term ap1 high 0#usize=ok (i0,t0))
    (term1 : FJm_LibraStages.term ap1 high 1#usize=ok (i1,t1))
    (term2 : FJm_LibraStages.term ap1 high 2#usize=ok (i2,t2))
    (term3 : FJm_LibraStages.term ap1 high 3#usize=ok (i3,t3))
    (totals : FJm_LibraStages.totals (Array.make 4#usize [t0,t1,t2,t3])=ok (first2,first3,all))
    (finish : FJm_LibraStages.finish side low i3 first2 first3 all q4 q16 ap1 before cursor=ok (.cont (cursor,after))) :
    FIo_Native.weights.factored_s2_libra_weights_loop.body ap0 ap1 extra iter before=ok (.cont (cursor,after)) := by
  rw [JGs_LibraProgram.source]
  unfold JGs_LibraProgram.body
  simp only [next,bind_tc_ok,Aeneas.Std.uncurry,powers,scalar,term0,term1,term2,term3,totals,finish]
#print axioms source

theorem scalar0 : FIo_Native.weights.Weights.scalar_factor JGs_Libra.row0 JGq_Powers0.a4=ok JGs_LibraScale0.value := by
  with_unfolding_all exact JGs_LibraScale0.source
#print axioms scalar0
theorem scalar1 : FIo_Native.weights.Weights.scalar_factor JGs_Libra.row1 JGq_Powers0.a4=ok JGs_LibraScale1.value := by
  with_unfolding_all exact JGs_LibraScale1.source
#print axioms scalar1
end AspisR1.JGs_LibraForward
end
