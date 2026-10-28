import R1Z.PV_DL_ResumeAudit
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_ResumeReplay
set_option autoImplicit false
theorem encoder {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_DL_EncoderNative.value inst q p=PV_CB_OwnedEncoder.owned.encoder inst q p :=
  PV_DL_EncoderNative.source_reference inst q p

theorem vector {T : Type} (N : Usize) (v : alloc.vec.Vec T) :
    PV_DL_ArrayNative.reference N v=ok (PV_DL_ArrayOwnership.value N v) :=
  PV_DL_ArrayNative.source_reference N v

theorem sha (compress : PV_DL_ShaFinal.State → List U8 → Result PV_DL_ShaFinal.State)
    (core : PV_DL_ShaFinal.Core) (buffer : Array U8 64#usize) (pos : Usize) (h : pos.val<64) :
    PV_DL_ShaFinal.reference compress core buffer pos=PV_DL_ShaFinal.value compress core buffer pos :=
  PV_DL_ShaFinal.source_reference compress core buffer pos h

#print axioms R1Z.PV_DL_EncoderNative.selected_native
#print axioms R1Z.PV_DL_ArrayNative.selected_native
#print axioms R1Z.PV_DL_ShaRestoration.selected_native
#print axioms R1Z.PV_DL_DigestFinal.selected_native
#print axioms R1Z.PV_DL_FixedFinal.selected_native
#print axioms R1Z.PV_DL_UpdateSelected.selected_native
#print axioms R1Z.PV_DL_DefaultNative.consumed
#print axioms R1Z.PV_DL_CtSelected.selected_native
#print axioms R1Z.PV_DL_NativeCohort.slots
#print axioms encoder
#print axioms vector
#print axioms sha
end R1Z.PV_DL_ResumeReplay
