import NDF_Reference.Funs
import Port3_BatchStd
import AspisR1PublicPreparation.Funs
set_option autoImplicit false
namespace NDF_ScalarBridge
open Aeneas Aeneas.Std Result

theorem key (keys : Array U64 16#usize) (i : Usize) :
    NDF_Reference.batch_key_at_ref keys i = Array.index_usize keys i := rfl

theorem same_index (values : Array U32 16#usize) (i : Usize) (v : U32) :
    NDF_Reference.same_batch_index_ref values i v = AspisR1.Port3_BatchStd.sameIndex values i v := by
  unfold NDF_Reference.same_batch_index_ref AspisR1.Port3_BatchStd.sameIndex
  rfl

theorem row (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    NDF_Reference.validated_row_ref r.row = AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.row r := rfl

theorem framed (r : AspisR1PublicPreparation.r1_wire.ValidatedRecord) :
    NDF_Reference.framed_ref r.framed = AspisR1PublicPreparation.r1_wire.ValidatedRecord.impl.framed r := rfl

theorem state {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (r : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
    NDF_Reference.state_ref r.state = AspisR1PublicPreparation.r1_wire.SemanticTranscript.impl.state D r := rfl

#print axioms key
#print axioms same_index
#print axioms row
#print axioms framed
#print axioms state
end NDF_ScalarBridge
