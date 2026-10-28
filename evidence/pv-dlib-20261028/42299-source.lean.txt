import R1Z.PV_DL_Audit
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_DL_Replay
set_option autoImplicit false

theorem encoder {E : Type} (inst : aspis_core.r0.scalar.CodeField E)
    (q : Array E 1024#usize) (p : aspis_core.r0.domain.Point E) :
    PV_CB_OwnedEncoder.owned.encoder inst q p=PV_DL_EncoderControl.value inst q p :=
  PV_DL_EncoderControl.source_reference inst q p

theorem padding {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : Array U8 64#usize) (pos : Usize) (suffix : Array U8 8#usize)
    (hp : pos.val<64) :
    PV_DL_FinalizeParam.reference compress state buffer pos suffix=
      PV_DL_FinalizeParam.model compress state buffer.val pos.val suffix.val :=
  PV_DL_FinalizeParam.source compress state buffer pos suffix hp

theorem truncation (side : digest.core_api.TruncSide) (n : Nat) (full : List U8)
    (h : n≤full.length) : (PV_DL_Truncation.value side n full).length=n :=
  PV_DL_Truncation.length side n full h

#print axioms encoder
#print axioms padding
#print axioms truncation
#print axioms PV_DL_DefaultNative.consumed
#print axioms PV_DL_Forwarding.ct_restoration
#print axioms PV_DL_Audit.padding_domain
end R1Z.PV_DL_Replay
