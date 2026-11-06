import NLB_EnteredCommonTransport
import NLP_FoldedValue
set_option autoImplicit false
noncomputable section
namespace NLP_TransportDomain
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- SAME folded-root projection adds precisely the missing C04 input domain. -/
def Domain (wr : NP6_StdModel.Reservation) {X : Type}
 (d : aspis_core.digest.Digest32 X) (ck proof pub : Slice U8) (hash : X)
 (pr : Slice U8) (p : verifier.Prepared) (root : Array U8 32#usize) : Prop :=
 NLB_ErrorTransport.MerkleDomain wr d ck proof pub hash pr p ∧ root.val=(pr.val.drop 7751).take 32
/-- Isolated domain construction, replacing L038's broad constructor search. -/
theorem at_branch (wr : NP6_StdModel.Reservation) {X : Type}
 (d : aspis_core.digest.Digest32 X) (ck proof pub : Slice U8) (hash : X)
 (reply : core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
 (p : verifier.Prepared) (a : verifier.Accumulator) (selected : Slice U8)
 (r : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) (root : Array U8 32#usize)
 (call : NJJ_Common.resume wr d ck proof pub .S2 hash=ok reply)
 (branch : core.result.Result.Insts.CoreOpsTry.branch reply=
  ok (core.ops.control_flow.ControlFlow.Continue (p,a)))
 (passed : ¬(a.next != NHT_Constants.compact.SPLIT)=true)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=7751#usize,«end»:=7783#usize}=ok selected)
 (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 selected=ok r)
 (unwrap : core.result.Result.unwrap core.fmt.DebugTryFromSliceError r=ok root) :
 Domain wr d ck proof pub hash proof p root :=
 ⟨NLB_ErrorTransport.at_branch wr d ck proof pub hash reply p a call branch passed,
  NLP_FoldedValue.source proof selected r root range copy unwrap⟩
set_option pp.proofs false
#print Domain
#print at_branch
#print axioms at_branch
end NLP_TransportDomain
