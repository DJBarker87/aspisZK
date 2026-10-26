import R1Z.ProverRw18CompressionWrite
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18WriterContext
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

def execute (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : Q) (out : Slice U8) : Result (Slice U8) := do
  let compressed ← @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
    tag values lambda
  ProverRw18QuarticWrite.source compressed out

theorem closed (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : Q) (out : Slice U8) :
    execute ops tag values lambda out=ProverRw18CompressionWrite.execute tag values lambda out := by
  unfold execute ProverRw18CompressionWrite.execute
  rw [ProverRw18ContextCompression.owned]

theorem bytes (ops : ProverRwFull.ExternalFuns) (tag : U32) (values : Slice U32)
    (lambda : Raw) (out : Slice U8) (htag : tag.val<2147483647)
    (hlambda : Canonical lambda) (bound : 16≤out.val.length) :
    ∃ result : Slice U8,execute ops tag values (full lambda) out=ok result ∧
      result.val=ProverRw18QuarticBytes.bytes
        (ProverRw18CompressionWrite.encoded tag values lambda)++out.val.drop 16 := by
  rw [closed]
  exact ProverRw18CompressionWrite.bytes tag values lambda out htag hlambda bound

#print axioms closed
#print axioms bytes
end R1Z.ProverRw18WriterContext
