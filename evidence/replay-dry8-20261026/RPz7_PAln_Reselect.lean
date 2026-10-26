import RPz7_PSem_Accepted
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.PAln_Reselect
open S2W_AuthenticatedInputs
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem writer (ops : AdapterRw.Ops) (decode : HeaderDecode)
    (H : Bytes → State) (old selected : AdapterRw.LeadInputs.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (oldCall : AdapterRw.first_decoded ops old pub proof split=ok (.Ok saved))
    (selectedCall : AdapterRw.first_decoded ops selected pub proof split=ok (.Ok saved))
    (join : CheckpointWriterConeJoin ops decode H selected pub proof split) :
    CheckpointWriterConeJoin ops decode H old pub proof split := by
  constructor
  · intro out call
    have eq : saved=out := core.result.Result.Ok.inj (Result.ok.inj (oldCall.symm.trans call))
    subst out
    exact join.header saved selectedCall
  · intro out call
    have eq : saved=out := core.result.Result.Ok.inj (Result.ok.inj (oldCall.symm.trans call))
    subst out
    exact join.size saved selectedCall

#print axioms writer
end AspisR1.PAln_Reselect
end
