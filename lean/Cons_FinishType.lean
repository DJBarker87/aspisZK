import Cons_Finish
import Cons_Native
set_option autoImplicit false
set_option pp.fullNames true
#check @AspisR1.Cons_Finish.Outcome
namespace AspisR1.Cons_FinishType
open Aeneas Aeneas.Std
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
def check {F : Type} (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (t : Cons_Native.Witness) (proof : Slice U8) (saved : alloc.vec.Vec U8)
    (H : Bytes → State) (stored pub : Bytes)
    (tx1p : AspisR1CurrentCaller.verifier.Prepared) (parsed : OraclePortCompactDraft.Parsed)
    (trace : List (Bytes × State)) : Prop :=
  Cons_Finish.Outcome finish t.v2 t.p2 {t.returned2 with weights := t.back2 t.flushed2}
    proof saved H stored pub tx1p parsed trace
end AspisR1.Cons_FinishType
