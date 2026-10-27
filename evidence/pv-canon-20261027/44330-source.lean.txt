import R1Z.PV_Canon_CanonicalInjective
import R1Z.PV_Canon_FieldMeaning
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std ProverRwFull
 theorem canonical_qinjective (x y : aspis_core.field.QM31) (hx : Q x) (hy : Q y)
    (h : decodeQ x = decodeQ y) : x=y := by
  have a : x.c0.a=y.c0.a := canonical_injective _ _ hx.1.1 hy.1.1 (by
    change (decodeQ x).re.re=(decodeQ y).re.re
    exact congrArg (fun z => z.re.re) h)
  have b : x.c0.b=y.c0.b := canonical_injective _ _ hx.1.2 hy.1.2 (by
    change (decodeQ x).re.im=(decodeQ y).re.im
    exact congrArg (fun z => z.re.im) h)
  have c : x.c1.a=y.c1.a := canonical_injective _ _ hx.2.1 hy.2.1 (by
    change (decodeQ x).im.re=(decodeQ y).im.re
    exact congrArg (fun z => z.im.re) h)
  have d : x.c1.b=y.c1.b := canonical_injective _ _ hx.2.2 hy.2.2 (by
    change (decodeQ x).im.im=(decodeQ y).im.im
    exact congrArg (fun z => z.im.im) h)
  change (aspis_core.field.QM31.mk ⟨x.c0.a,x.c0.b⟩ ⟨x.c1.a,x.c1.b⟩) =
    (aspis_core.field.QM31.mk ⟨y.c0.a,y.c0.b⟩ ⟨y.c1.a,y.c1.b⟩)
  rw [a,b,c,d]
#print axioms canonical_qinjective
end R1Z.PV_Canon
