import NNG_DecoderGraph345
import NNG_ChildSource345
import NNG_Caller345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_NativeCaller345
open Aeneas Aeneas.Std NMT_345 RSL

theorem decoded (b : Slice U8) (st : Statement) (h : decodeCall b=.ok (.Ok st)) :
 LIBC_S1.decode (LIB_Carriers.bytes b)=some st := by
 rw [NNG_DecoderGraph345.source] at h
 cases hd : LIBC_S1.decode (LIB_Carriers.bytes b) with
 | none=>rw [hd] at h;cases h
 | some found=>rw [hd] at h;cases h;rfl
#print axioms decoded

/-- Both child clauses at the SAME native emitted arguments. Decode/validate
are reached-call equalities, not parent own-input assumptions. -/
theorem domain (publicBytes proof : Slice U8) (st : Statement) (k : Usize)
 (hd : decodeCall publicBytes=.ok (.Ok st)) (hv : validateCall st=.ok (.Ok ())) :
 TX1_328.Domain LIB_Instances.VL
 (NNG_ChildSource345.args (semanticValue st) publicBytes proof k) := by
 rw [NNG_ChildSource345.args_fields]
 constructor
 · exact LIB_S1.validated_public st ((LIBC_S1.valid_iff st).mpr hv)
 · exact NNG_P1880Discharge.decoder LIB_Instances.VL rfl
     (LIB_Carriers.bytes publicBytes) st (decoded publicBytes st hd)
#print axioms domain
end AspisR1.NNG_NativeCaller345
