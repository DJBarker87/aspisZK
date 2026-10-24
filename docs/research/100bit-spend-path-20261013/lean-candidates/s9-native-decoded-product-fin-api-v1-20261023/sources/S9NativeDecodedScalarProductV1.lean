import S9NativeInputProductWitnessV1
import S9ActualFinishDecodedStateV1
import AspisR1S5ClaimScalarEmbeddedProductSum
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9NativeDecodedScalarProductV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9NativeInputProductWitnessV1
abbrev ClaimW := AspisR1S5ClaimScalarEmbeddedProductSum.ClaimWide
abbrev ClaimQ := AspisR1S5ClaimScalarEmbeddedProductSum.ClaimQM

def toClaimW (w : NativeW) : ClaimW :=
  {c0:={c0:={a:=w.c0.c0.a,b:=w.c0.c0.b},c1:={a:=w.c0.c1.a,b:=w.c0.c1.b}},
   c1:={c0:={a:=w.c1.c0.a,b:=w.c1.c0.b},c1:={a:=w.c1.c1.a,b:=w.c1.c1.b}}}
def toClaimQ (q : NativeQ) : ClaimQ :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}

def toCurrentQ (q : NativeQ) : AspisR1CurrentWide.field.QM31 :=
  {c0:={a:=q.c0.a,b:=q.c0.b},c1:={a:=q.c1.a,b:=q.c1.b}}
def decodeNative (w : NativeW) : AspisWideTower.WideExact :=
  AspisR1CurrentWide.Proof.decodeWide
    (AspisR1S9ActualPairWideCanonicalV1.toCurrent w)
def scalarEmbed (q : NativeQ) : AspisWideTower.WideExact :=
  algebraMap AspisV8R15.ExactTowerBase.QM31Exact AspisWideTower.WideExact
    (AspisR1CurrentWide.Proof.decodeQM (toCurrentQ q))

/-- Literal word-preserving claim/native carrier adapters only. -/
theorem claim_decode_native (w : NativeW) :
    AspisR1CurrentPreparedClaim.Concrete.decode (toClaimW w)=decodeNative w := by rfl
theorem claim_scalar_embed_native (q : NativeQ) :
    AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed (toClaimQ q)=scalarEmbed q := by rfl

/-- The retained S4 scalar product and retained S5 query product interpret
exactly the same eight/four native input words. No source/Can premise. -/
theorem source_scalar_product_query (w : NativeW) (q : NativeQ) :
    AspisR1FastDotsTailFieldProductRootV1.scalarProduct (sourcePair (w,q))=
      AspisR1FinishDotReturnedFieldProductV1.queryProductWide
        (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishE (toClaimW w))
        (AspisR1S5ClaimScalarConcreteQRawTrace.claimToFinishQM (toClaimQ q)) := by rfl

/-- Reuse the EXISTING proved scalar-embedded query multiplication theorem;
this specialization changes only exact native/claim coordinate carriers. -/
theorem native_scalar_product_eq_decoded_mul_embed (w : NativeW) (q : NativeQ) :
    AspisR1FastDotsTailFieldProductRootV1.scalarProduct (sourcePair (w,q))=
      decodeNative w * scalarEmbed q := by
  rw [source_scalar_product_query]
  have h := AspisR1S5ClaimScalarEmbeddedProductSum.queryProductWide_eq_decode_mul_scalar
    (toClaimW w) (toClaimQ q)
  simpa only [claim_decode_native,claim_scalar_embed_native] using h

#print axioms claim_decode_native
#print axioms claim_scalar_embed_native
#print axioms source_scalar_product_query
#print axioms native_scalar_product_eq_decoded_mul_embed
end AspisR1S9NativeDecodedScalarProductV1
