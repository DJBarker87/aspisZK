import R1Z.ProverRw18QuarticBytes
import R1Z.ProverRw18FieldReference
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18CompressionWrite
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning

def execute (tag : U32) (values : Slice U32) (lambda : Q) (out : Slice U8) : Result (Slice U8) := do
  let compressed ← PV_RW_CompressClosed.owned tag values lambda
  ProverRw18QuarticWrite.source compressed out

def encoded (tag : U32) (values : Slice U32) (lambda : Raw) : Q :=
  full (ProverRw18FieldEncode.encode
    (ProverRw18FieldReference.value tag values.val (decode lambda)))

theorem exact_write (tag : U32) (values : Slice U32) (lambda : Raw) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) (bound : 16≤out.val.length) :
    execute tag values (full lambda) out=
      ok (ProverRw18QuarticWrite.output (encoded tag values lambda) out) := by
  unfold execute
  rw [ProverRw18FieldReference.closed tag values lambda htag hlambda]
  change ProverRw18QuarticWrite.source (encoded tag values lambda) out=_
  exact ProverRw18QuarticWrite.exact_write _ out bound

theorem bytes (tag : U32) (values : Slice U32) (lambda : Raw) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,execute tag values (full lambda) out=ok result ∧
      result.val=ProverRw18QuarticBytes.bytes (encoded tag values lambda)++out.val.drop 16 :=
  ⟨_,exact_write tag values lambda out htag hlambda bound,
    ProverRw18QuarticBytes.output_value _ out bound⟩

#print axioms exact_write
#print axioms bytes
end R1Z.ProverRw18CompressionWrite
