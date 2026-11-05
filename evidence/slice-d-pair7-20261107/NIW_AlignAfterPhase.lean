import NIW_AlignSharedPhase
import NIT_RegularChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignAfterPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
variable [FIo_Native.Allocation]

inductive Log where
 | rejected
 | unshared (tail : NIW_AlignTailPhase.Log)
 | shared (tail : NIW_AlignSharedPhase.Log)

def run (c : Context) (shared : Bool) (parts : Parts) (reply : RU) : Result NR × Log :=
 match reply with
 | .Err err => (ok (.Err err),.rejected)
 | .Ok _ => if shared then
   let tail := NIW_AlignSharedPhase.run c parts
   (tail.1,.shared tail.2)
  else
   let tail := NIW_AlignTailPhase.run c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress
   (tail.1,.unshared tail.2)

theorem trace (c : Context) (shared : Bool) (parts : Parts) (reply : RU)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) :
 NIT_RegularChain.After c shared parts reply (run c shared parts reply).1 := by
 cases reply with
 | Err err => exact .rejected err
 | Ok unit =>
  cases unit
  cases shared with
  | false => exact .unshared _ rfl (NIW_AlignTailPhase.trace c.w c.f c.ap0 c.ap1 parts c.kappa
    c.lowAddress domain.s2 (NIT_PairDomain.message_size _ _ _ _ domain) c0 c1 domain.extra cp domain.kappa)
  | true => exact .shared _ rfl (NIW_AlignSharedPhase.trace c parts domain c0 c1 cp)

#print axioms trace
end AspisR1.NIW_AlignAfterPhase
