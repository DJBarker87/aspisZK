import NIW_AlignAfterPhase
import NJU_WeakPairDomain
import NJU_WeakRegularChain
import NJU_WeakAlignSharedPhase
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJU_WeakAlignAfterPhase
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl
open NIW_AlignAfterPhase
variable [FIo_Native.Allocation]

/- Generalized domain only. Original data/trace/evaluator definitions reused. -/
theorem trace (c : Context) (shared : Bool) (parts : Parts) (reply : RU)
 (domain : NJU_WeakPairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (c0 : canonical c.ap0.value) (c1 : canonical c.ap1.value) (cp : canonical parts) :
 NIT_RegularChain.After c shared parts reply (run c shared parts reply).1 := by
 cases reply with
 | Err err => exact .rejected err
 | Ok unit =>
  cases unit
  cases shared with
  | false => exact .unshared _ rfl (NIW_AlignTailPhase.trace c.w c.f c.ap0 c.ap1 parts c.kappa
    c.lowAddress domain.s2 domain.size c0 c1 domain.extra cp domain.kappa)
  | true => exact .shared _ rfl (NJU_WeakAlignSharedPhase.trace c parts domain c0 c1 cp)


#print axioms trace
end AspisR1.NJU_WeakAlignAfterPhase
