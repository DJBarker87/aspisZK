import R1Z.PV_Src_DynamicCallEquation
import R1Z.PV_Src_ExternalReference

/-! The complete Result equation at the explicitly pure extracted dictionary.
The shipped Records-to-reference association is still a separate P6 obligation. -/
set_option autoImplicit false
namespace R1Z.PV_Src_PureCallEquation
open Aeneas Aeneas.Std Result
open BuilderForestAdmissionPort BuilderForestAdmissionPort.pool_v1

theorem call
    (input : pair_forest_trace.PoolV1PairForestInputNoteWitnessV1)
    (out : U32) (rec : Option payment_relation.PoolV1OutputNoteWitnessV1)
    (chg : payment_relation.PoolV1OutputNoteWitnessV1)
    (s : pair_tree_profile.PoolV1PairLiveSnapshotV1) (asset : U32) :
    @Records.call (@PV_Src_RecordDynamic.dictionary PV_Src_ExternalReference.dictionary)
      input out rec chg s asset =
      (do let roots ← @pair_trace.pair_empty_roots PV_Src_ExternalReference.dictionary
          ok (PV_Src_DynamicCallEquation.returned roots input out rec chg s asset)) :=
  @PV_Src_DynamicCallEquation.call PV_Src_ExternalReference.dictionary input out rec chg s asset

#print axioms call
end R1Z.PV_Src_PureCallEquation
