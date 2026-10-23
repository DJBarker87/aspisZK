import S9RegularTensorReadbackV1
import S9ConstructorTableNativeTensorV1
import S9NativeScalarTensorEmbedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9RegularTensorModelWeightV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9RegularKindExecutionV1
open AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9FactorTableSemanticsV1 (Table Meaning)
open AspisR1S9NativeDecodedScalarProductV1 (scalarEmbed)
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

/-- A SAME regular source operand read has exactly its SAME constructor-table
high tensor meaning. Input meanings/canonicality here are existing complete
constructor outputs; no desired scratch value or length is supplied. -/
theorem actual_regular_tensor_read_model_weight
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w))
    (kind : Usize) (hk : (rowOfKind kind).val<5) (f : Slice U8)
    (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (e : Execution (fromCtorWeights w) kind f 64#usize ap0 ap1 scratch scratchOut parts partsOut)
    (j : Usize) (hj : j.val<64) (q : NQ)
    (hr : Slice.index_usize (alloc.vec.Vec.deref scratchOut) j=.ok q) :
    scalarEmbed q=algebraMap AspisR1CurrentWide.Proof.ExactQM AspisWideTower.WideExact
      (highProduct (model (rowOfKind kind).val) j.val) := by
  have hs := AspisR1S9RegularTensorReadbackV1.execution_tensor_readback
    (fromCtorWeights w) kind f 64#usize ap0 ap1 scratch scratchOut parts partsOut e
  have hread : Slice.index_usize (Execution.tensorOut e) j=.ok q :=
    (congrArg (fun s => Slice.index_usize s j) hs).symm.trans hr
  have ht := native_tensor_success_table w model hm hc (rowOfKind kind) hk
    (Execution.input e) (Execution.tensorOut e) (Execution.tensor e)
  have hv := ht j q hread hj
  exact (AspisR1S9NativeScalarTensorEmbedV1.scalar_embed_tensor q).trans
    (congrArg (algebraMap AspisR1CurrentWide.Proof.ExactQM AspisWideTower.WideExact) hv)

#print axioms actual_regular_tensor_read_model_weight
end AspisR1S9RegularTensorModelWeightV1
