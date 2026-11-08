import NNG_ChildSource345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_SplitByte345
open Aeneas Aeneas.Std NMT_345

/-- Internal source fact at data[1] as usize. It is not a parent premise. -/
theorem value (b : U8) : (UScalar.cast .Usize b).val=b.val := by scalar_tac
#print axioms value

theorem bound (b : U8) : (UScalar.cast .Usize b).val≤UScalar.cMax .Usize := by
 rw [value]
 have h := b.hmax
 scalar_tac
#print axioms bound

theorem observation (env : RSL.Env) (pub : Public) (publicBytes proof : Slice U8) (b : U8) :
 LIB_Carriers.resultObs NNG_ChildSource345.port
 (NNG_ChildSource345.events env pub publicBytes proof (UScalar.cast .Usize b))
 (NNG_ChildSource345.call env pub publicBytes proof (UScalar.cast .Usize b))=
 NNG_Producer328.producer (NNG_ChildSource345.args pub publicBytes proof (UScalar.cast .Usize b)) env :=
 NNG_ChildSource345.observation env pub publicBytes proof _ (bound b)
#print axioms observation
end AspisR1.NNG_SplitByte345
