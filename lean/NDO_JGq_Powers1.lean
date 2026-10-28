import NDO_JGq_Powers1Step0
import NDO_JGq_Powers1Step1
import NDO_JGq_Powers1Step2
import NDO_JGq_Powers1Step3
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_Powers1
open Aeneas Aeneas.Std Result ControlFlow
def states : Nat → S
  | 0 => (a0,p0,0#usize)
  | 1 => (a1,p1,1#usize)
  | 2 => (a2,p2,2#usize)
  | _ => (a3,p3,3#usize)
theorem source : FIo_Native.weights.powers 4#usize x=ok a4 := by
  unfold FIo_Native.weights.powers FIo_Native.weights.powers_loop
  apply JGo_TX2_LoopChain.source
    (fun s : S=>match s with | (out,p,i)=>FIo_Native.weights.powers_loop.body x out p i)
    states 3 a4
  · intro i hi
    interval_cases i
    · exact step0
    · exact step1
    · exact step2
  · exact step3
#print axioms source
end AspisR1.JGq_Powers1
end
