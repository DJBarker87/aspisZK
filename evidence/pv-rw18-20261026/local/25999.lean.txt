import R1Z.ProverRw18CallbackWrite
import R1Z.ProverRw18FinalPower16
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ComponentGate
open Aeneas Aeneas.Std Result ProverRw18FieldMeaning
variable [ProverRwFull.ExternalTypes]

-- Joint consumer of the arity16 value, final-power and byte theorems.
-- It retains both original-source obligations and is not a release theorem.
theorem gate (ops : ProverRwFull.ExternalFuns) (extracted : ProverRw18ContextJoin.Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted=
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops))
    (tag : U32) (values : Array U32 16#usize) (lambda : Raw) (initialOut : Q) (out : Slice U8)
    (htag : tag.val<2147483647) (hlambda : Canonical lambda) (bound : 16≤out.val.length) :
    ops.op223 tag (Array.to_slice values) (full lambda)=
      ok (ProverRw18FullCarrier.encode (ProverRw18CallbackWrite.value tag values (full lambda))) ∧
    ProverRwDictionaryTower.mapResult Prod.snd
      (PV_RW_IteratorStateLoop.run ops (full lambda)
        (⟨Array.to_slice values,0⟩ : core.slice.iter.Iter U32) (initialOut,full lambda))=
          ok (full (ProverRw18FieldEncode.encode ((decode lambda)^17))) ∧
    ∃ result : Slice U8,ProverRw18CallbackWrite.execute ops tag values (full lambda) out=ok result ∧
      result.val=ProverRw18QuarticBytes.bytes (ProverRw18FullCarrier.encode
        (ProverRw18CallbackWrite.value tag values (full lambda)))++out.val.drop 16 := by
  have canonical : ProverRw18FullCarrier.canonical (full lambda) := by
    unfold ProverRw18FullCarrier.canonical
    rw [ProverRw18FullCarrier.raw_full]
    exact hlambda
  exact ⟨ProverRw18CallbackModel.value ops extracted source_law context_identity tag values (full lambda) htag canonical,
    ProverRw18FinalPower16.combined ops values lambda initialOut hlambda,
    ProverRw18CallbackWrite.bytes ops extracted source_law context_identity tag values (full lambda) out htag canonical bound⟩

#print axioms gate
end R1Z.ProverRw18ComponentGate
