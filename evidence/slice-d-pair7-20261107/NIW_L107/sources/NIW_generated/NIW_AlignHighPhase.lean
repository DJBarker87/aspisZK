import NIW_AlignTailPhase
import NIT_SharedChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignHighPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

def run (c : Context) (w : Ref W) (parts : Parts) (reply : RU) : Result NR × Option NIW_AlignTailPhase.Log :=
 match reply with
 | .Err err => (ok (.Err err),none)
 | .Ok _ =>
  let tail := NIW_AlignTailPhase.run w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress
  (tail.1,some tail.2)

theorem trace (c : Context) (w : Ref W) (parts : Parts) (reply : RU)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value)
 (ce : NHI_CellCanon.array w.value.extra) (cp : canonical parts) (ck : canonE c.kappa) :
 NIT_SharedChain.High c w parts reply (run c w parts reply).1 := by
 cases reply with
 | Err err => exact .rejected err
 | Ok unit =>
  cases unit
  exact .returned _ (NIW_AlignTailPhase.trace w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress s2 size c0 c1 ce cp ck)

#print axioms trace
end AspisR1.NIW_AlignHighPhase
