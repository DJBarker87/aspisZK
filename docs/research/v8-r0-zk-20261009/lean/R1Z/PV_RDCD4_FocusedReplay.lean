import R1Z.PV_RDCD4_FinalAudit
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_FocusedReplay
open Aeneas Aeneas.Std Result ProverRwFull

theorem v201 {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_RDCD4_V201.value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p :=
  PV_RDCD4_V201.source_reference inst q p

theorem v220 (poly : Array PV_RDCD4_LazyComponents.Q 28#usize)
    (challenge : PV_RDCD4_LazyComponents.Q) :
    PV_RDCD4_V220.source poly challenge=PV_RDCD4_V220.reference poly challenge :=
  PV_RDCD4_V220.source_reference poly challenge

theorem v237 {T : Type} (core : Result T) :
    (do let v ← PV_DL_DefaultBuffer.model core;ok (PV_DL_WrapLaw.observe v))=
    (do let c ← core;let v ← PV_DL_Wrap.wrap_reference c;ok (PV_DL_WrapLaw.observeReference v)) :=
  PV_RDCD4_V237.complete core

#print axioms v201
#print axioms v220
#print axioms v237
end R1Z.PV_RDCD4_FocusedReplay
