import XSa_DotWord
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSa_FinishWord

theorem reduce (x : U64) : _root_.aspis_core.field.M31.reduce_u64 x =
 ok (AspisR1EbyKFinish.Proof.word x) := by
 obtain ⟨z,hz,hv,hc⟩ := AspisR1.LPf_CoreReduction.source x
 have he : z=AspisR1EbyKFinish.Proof.word x := by
   apply UScalar.eq_of_val_eq
   rw [hv,AspisR1CanonicalDotFinish.Proof.canonicalWord_val]
 change XRn_Join_Field.field.M31.reduce_u64 x=ok (AspisR1EbyKFinish.Proof.word x)
 simp only [XRn_Join_Field.field.M31.reduce_u64,XRs_BaseMultiply.same_reducer,hz,bind_tc_ok]
 exact congrArg ok he

#print axioms reduce
end XSa_FinishWord
