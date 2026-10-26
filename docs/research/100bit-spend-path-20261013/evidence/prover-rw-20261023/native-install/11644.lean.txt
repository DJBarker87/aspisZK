import R1Z.ProverRwDictionaryOption
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryEmbedding
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower

-- scalar.rs WideExact::from_m31 is the retained qFrom body followed by
-- WideExact::from_qm31. These callees normalize arbitrary raw representatives.
def embed (x : U32) : Result W := mapResult fromW (do
  let q ← ProverRwDictionaryScalar.qFrom x
  AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31 q)

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryOption.selected ops with op110 := embed}

theorem installed (ops : ExternalFuns) (x : U32) :
    (selected ops).op110 x = mapResult fromW (do
      let q ← ProverRwDictionaryScalar.qFrom x
      AspisR1ProducerRelease47.field.wide_exact.WideExact.from_qm31 q) := rfl

/-- The query-field embedding uses the same selected QM31-from-base body,
then the same selected wide embedding; arbitrary machine failures are preserved. -/
theorem composition (ops : ExternalFuns) (x : U32) :
    (selected ops).op110 x = (do
      let q ← (selected ops).op108 x
      (selected ops).op45 q) := by
  change mapResult fromW _ = (do
    let q ← mapResult fromQ (ProverRwDictionaryScalar.qFrom x)
    ProverRwDictionaryTower.wEmbed q)
  cases h : ProverRwDictionaryScalar.qFrom x with
  | ok q => simp only [h,mapResult,bind_tc_ok,ProverRwDictionaryTower.wEmbed,native_q_roundtrip]
  | fail e => rfl
  | div => rfl

#print axioms installed
#print axioms composition
end R1Z.ProverRwDictionaryEmbedding
