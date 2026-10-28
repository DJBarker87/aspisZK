import NDO_JGq_PowersKStep0
import NDO_JGq_PowersKStep1
import NDO_JGq_PowersKStep2
import NDO_JGq_PowersKStep3
import NDO_JGq_PowersKStep4
import NDO_JGq_PowersKStep5
import NDO_JGq_PowersKStep6
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PowersK
open Aeneas Aeneas.Std Result ControlFlow
def states : Nat → S
  | 0 => (a0,p0,0#usize)
  | 1 => (a1,p1,1#usize)
  | 2 => (a2,p2,2#usize)
  | 3 => (a3,p3,3#usize)
  | 4 => (a4,p4,4#usize)
  | 5 => (a5,p5,5#usize)
  | _ => (a6,p6,6#usize)
theorem source : FIo_Native.weights.powers 7#usize x=ok a7 := by
  unfold FIo_Native.weights.powers FIo_Native.weights.powers_loop
  apply JGo_TX2_LoopChain.source
    (fun s : S=>match s with | (out,p,i)=>FIo_Native.weights.powers_loop.body x out p i)
    states 6 a7
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
    · exact step3
    · exact step4
    · exact step5
  · exact step6
#print axioms source
end AspisR1.JGq_PowersK
end
