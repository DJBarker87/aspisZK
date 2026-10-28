import R1Z.PV_DL_EncoderControl
import R1Z.PV_DL_EncoderPairs
import R1Z.ProverRwFullExternalFuns
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_EncoderSelected
set_option autoImplicit false
variable [types : ExternalTypes]

/-- Candidate installation of the structurally transported encoder. Source
body/iterator checks and native finite evidence are recorded separately. -/
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op79 := fun inst q p => PV_DL_EncoderControl.value inst q p}

theorem selected_callback (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (q : Array E 1024#usize)
    (p : aspis_core.r0.domain.Point E) :
    (selected ops).op79 inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p :=
  (PV_DL_EncoderControl.source_reference inst q p).symm

theorem consumed (ops : ExternalFuns) {E : Type}
    (inst : aspis_core.r0.scalar.CodeField E) (q : Array E 1024#usize)
    (p : aspis_core.r0.domain.Point E) :
    @aspis_core.r0.encoder.eval_message types (selected ops) E inst q p=
      PV_CB_OwnedEncoder.owned.encoder inst q p :=
  selected_callback ops inst q p

theorem pairs_complete {E : Type} (q : Array E 1024#usize) :
    (PV_DL_EncoderPairs.chunks q.val).length=512 :=
  PV_DL_EncoderPairs.message_count q.val q.property

#print axioms selected
#print axioms selected_callback
#print axioms consumed
#print axioms pairs_complete
end R1Z.PV_DL_EncoderSelected
