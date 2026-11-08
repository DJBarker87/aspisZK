import NNG_NativeCaller345
import NNG_SplitByte345
import NNG_Events345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_FirstNative345
open Aeneas Aeneas.Std NMT_345 RSL NMT_CallTree

/-- Concrete complete328 root installed at the emitted345 call occurrence.
The source cast bound and both RowSpec clauses are discharged here. -/
theorem occurrence (publicBytes proof : Slice U8) (st : Statement) (b : U8) (env : Env)
 (hd : decodeCall publicBytes=.ok (.Ok st)) (hv : validateCall st=.ok (.Ok ())) :
 Spec.call (TX1_328.Domain LIB_Instances.VL) (TX1_328.Ref LIB_Instances.VL LIB_Instances.P)
 (NNG_ChildSource345.args (semanticValue st) publicBytes proof (UScalar.cast .Usize b)) env
 (NNG_Observed136.observation NNG_ChildSource345.port (NNG_Events345.events env)
 (invoke "TX1:328/first_decoded" (semanticValue st,publicBytes,proof,UScalar.cast .Usize b)
 (NNG_ChildSource345.call env (semanticValue st) publicBytes proof (UScalar.cast .Usize b)))) := by
 rw [NNG_Events345.observation env _ _ _ _ (NNG_SplitByte345.bound b)]
 have h := NNG_NativeCaller345.domain publicBytes proof st (UScalar.cast .Usize b) hd hv
 exact ⟨h,NNG_Candidate328.candidate _ env h⟩
#print axioms occurrence
end AspisR1.NNG_FirstNative345
