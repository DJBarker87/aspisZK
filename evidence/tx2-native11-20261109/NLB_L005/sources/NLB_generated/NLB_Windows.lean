import NLB_Fold
import NKO_C02Install
import NKO_C03Install
import NKO_C05Install
import NKO_C08Install
import NKO_C09Install
import NKO_QueryReturnG
import NKE_CommonCalls
import NKE_CommonNative
set_option autoImplicit false
noncomputable section
namespace NLB_Parent
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
abbrev Resume := ∀ {H : Type}, aspis_core.digest.Digest32 H → Slice U8 → Slice U8 → Slice U8 → H → R (verifier.Prepared × verifier.Accumulator)
/-- Fixed release finish; no operation dictionary or observer parameter. -/
def finish (r : NP6_StdModel.Reservation) : Finish :=
 fun v p a _ => NHT_ResultPort.action (Port3_NativeFinishBody.verifier.finish_relation (NIG_Slots.installed r) v p a none)
/-- Forward transforms at every occurrence. The incoming event's reply is
ignored at ALL nine sites. The only open call implementations are resume and
batch_merkle. These parameters are auxiliary until exact child packets arrive.
Pending and flush use the retained native induction; query includes the
retained full owned return/destructure G; finish uses its generalized (aw) G. -/
def window (rr fr : NP6_StdModel.Reservation) (loc : NIW_AlignFinishComposed.Locations)
 (resume : Resume) (merkle : Merkle) {H : Type} (d : aspis_core.digest.Digest32 H) (hash : H) : Event → Event
 | .resume ck proof pub _ => .resume ck proof pub (resume d ck proof pub hash)
 | .powers gamma _ => .powers gamma (NHT_PacketOps.powers 29#usize gamma)
 | .inactive bytes _ => .inactive bytes (NJC_ClosedCalls.inactive bytes)
 | .merkle proof p root _ => .merkle proof p root (merkle d proof p root 1#usize hash)
 | .geometry queries next _ => .geometry queries next (NJC_ClosedCalls.geometry queries next 22#usize)
 | .pending weights _ => .pending weights (NKE_CommonNative.pendingG rr weights)
 | .query proof p a g geometry pending _ => .query proof p a g geometry pending
     (NKO_QueryReturnG.G (NKE_QueryReturn.observed (NJJ_Common.query proof p a g none geometry pending 22#usize)))
 | .flush pending weights _ => .flush pending weights (ok (NJJ_Flush.output pending))
 | .finish v p a _ => .finish v p a (NHT_ResultPort.action (NJF_FinishObserved.G fr loc v p a).1)
end NLB_Parent
