import NCJ_WordIdentity
import NBG_FieldDischarge
set_option autoImplicit false
namespace NDL_ArithmeticCalls
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Exact emitted mixed-product value on the caller-established domain.
No native multiplication is performed by the corresponding opaque log. -/
theorem mixed (x : NE) (y : NQ) (reply : NE) (hx : canonE x)
    (value : ew reply=(mulQ (qw x.c0) (NBG_FieldDischarge.modQ (qw y)),
      mulQ (qw x.c1) (NBG_FieldDischarge.modQ (qw y)))) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 x y=ok reply := by
  obtain ⟨z,run,_,hz⟩ := NBG_FieldDischarge.wide_qm x y hx
  have same := NCJ_WordIdentity.wide z reply (hz.trans value.symm)
  simpa only [same] using run

theorem scale (x : NE) (s : U32) (reply : NE)
    (value : ew reply=(NBG_FieldDischarge.scaleQ (qw x.c0) (s.val%2147483647),
      NBG_FieldDischarge.scaleQ (qw x.c1) (s.val%2147483647))) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 x s=ok reply := by
  obtain ⟨z,run,_,hz⟩ := NBG_FieldDischarge.wide_scale x s
  have same := NCJ_WordIdentity.wide z reply (hz.trans value.symm)
  simpa only [same] using run

theorem add (x y reply : NE) (hx : canonE x) (hy : canonE y)
    (value : ew reply=(addQ (qw x.c0) (qw y.c0),addQ (qw x.c1) (qw y.c1))) :
    FIo_Native.aspis_core.field.wide_exact.WideExact.add x y=ok reply := by
  obtain ⟨z,run,_,hz⟩ := NBG_WideCarriers.wide_add x y hx hy
  have same := NCJ_WordIdentity.wide z reply (hz.trans value.symm)
  simpa only [same] using run

#print axioms mixed
#print axioms scale
#print axioms add
#print axioms NBG_FieldDischarge.wide_qm
#print axioms NBG_FieldDischarge.wide_scale
#print axioms NBG_WideCarriers.wide_add
end NDL_ArithmeticCalls
