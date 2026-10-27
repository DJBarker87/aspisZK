import JHe_ReferenceRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_WriterSelected
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

def saved : alloc.vec.Vec U8 := Classical.choose JHe_Run.inhabited
def execution : JHe_Run.Run saved := Classical.choice (Classical.choose_spec JHe_Run.inhabited).2.2

theorem returns : verifier.candidate.tx1 installed digest JHe_Run.semantic
    JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=ok (.Ok saved) :=
  (Classical.choose_spec JHe_Run.inhabited).1
#print axioms returns

theorem length : saved.val.length=1768 := (Classical.choose_spec JHe_Run.inhabited).2.1
#print axioms length

theorem original : Tx1Q_Install.writer digest execution.p
    {execution.out with weights:=⟨execution.flushed.val,execution.flushed.property⟩}
    JFx_NativeBytes.proof JFx_NativeBytes.publicInput ()=ok saved :=
  JHe_ReferenceRun.writer saved execution
#print axioms original
end AspisR1.JHe_WriterSelected
end
