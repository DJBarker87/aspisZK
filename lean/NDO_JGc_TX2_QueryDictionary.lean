import NDO_JFr_TX2_DotsBinding
import Port3_QueryStage
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_QueryDictionary
open Aeneas Aeneas.Std Result
abbrev Ops := Port3_NativeQueryBody.Ops

def input (seed : Ops) : Ops :=
  {seed with
    op20 := FIp_DotsAdapter.dots
    op17 := FIp_CircleQuery.circle
    widePartialEq := FIp_Equality.dictionary
    op19 := Port3_QueryStage.mark}
def ops (seed : Ops) : Ops := JFn_ArrayBuilder.ops (input seed)

theorem release (seed : Ops) : Port3_QueryStage.release (JFr_TX2_DotsBinding.ops seed)=ops seed := by
  unfold Port3_QueryStage.release JFr_TX2_DotsBinding.ops ops input JFn_ArrayBuilder.ops
    Port4C_RowStd.install Port3_NativeRowFrame.install Port4C_QueryStd.install
    Port5Q1_QueryPorts.install SAQ_Decoder.install SAQ_LineQuery.install
    SAQ_QuerySource.install SAQ_Arithmetic.install SAQ_Query.install
  rfl

theorem fields (seed : Ops) :
    (ops seed).op11=Port4B_Opening.opening ∧
    (ops seed).op18=Port5Q1_GeometryBinding.forQuery ∧
    (ops seed).op20=FIp_DotsAdapter.dots ∧
    (ops seed).op17=FIp_CircleQuery.circle ∧
    (ops seed).op16=SAQ_LineQuery.line ∧
    (ops seed).widePartialEq=FIp_Equality.dictionary ∧
    (ops seed).op15=(fun _ _ _ => ok ()) ∧
    (ops seed).op19=Port3_QueryStage.mark := by
  unfold ops input JFn_ArrayBuilder.ops Port4C_RowStd.install
    Port3_NativeRowFrame.install Port4C_QueryStd.install Port5Q1_QueryPorts.install
    SAQ_Decoder.install SAQ_LineQuery.install SAQ_QuerySource.install
    SAQ_Arithmetic.install SAQ_Query.install
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem eqSelf (x : SAQ_WideABI.E) : FIp_Equality.eq x x=ok true := by
  simp [FIp_Equality.eq,FIp_Equality.qm]

theorem neSelf (x : SAQ_WideABI.E) :
    core.cmp.PartialEq.ne.trait_default FIp_Equality.dictionary x x=ok false := by
  simp only [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,FIp_Equality.dictionary,eqSelf,bind_tc_ok]
  rfl
#print axioms release
#print axioms fields
#print axioms eqSelf
#print axioms neSelf
end AspisR1.JGc_TX2_QueryDictionary
end
