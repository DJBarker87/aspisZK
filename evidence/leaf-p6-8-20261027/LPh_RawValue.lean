import RPu_FJf_RawReference
set_option autoImplicit false
namespace AspisR1.LPh.Raw
open Aeneas Aeneas.Std Result
open JFs_TX2_RawMap (pack)
open FJf_RawReference
/-- Named pairing for the scratch raw stub. No multiplication is admitted to
Lean from Kani; this is the existing checked emitted definition's value law. -/
theorem value (a b c d e f g h : U32) :
    FIo_Native.fast_pairing.canonical.Q.raw (pack a b c d) (pack e f g h)=
      ok (pack (raw0 a b c d e f g h) (raw1 a b c d e f g h)
        (raw2 a b c d e f g h) (raw3 a b c d e f g h)) :=
  FJf_RawReference.source a b c d e f g h
#print axioms value
#print axioms FJf_RawReference.source
end AspisR1.LPh.Raw
