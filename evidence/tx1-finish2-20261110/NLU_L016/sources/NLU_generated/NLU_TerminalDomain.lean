import NLU_State
import NLH_WrapperRoot
import FIq_Terminal
import NKQ_MaskCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLU_Terminal
open Aeneas Aeneas.Std Result AspisR1PublicPreparation FIq_Carriers
/-- Predicates on verify_finish's OWN public/challenge inputs. Canonical
claims/alpha are deliberately absent: the parent must derive those from the
SAME rounds/claims outputs before it may enter256. -/
structure InputDomain (pub : Public) (c : r1_wire.Challenges) : Prop where
 digest : NKR_DigestChildren.Domain (NKR_TermPublic.value (toPublic pub))
 asset : (NKR_TermPublic.value (toPublic pub)).asset_id.val < 2147483647
 zc : FIw_ArrayValue.canonical (mapArray toQ c.zc)
 lambda : FIv_NativeValue.Canon (toQ c.lambda)
 chi : FIv_NativeValue.Canon (toQ c.chi)
 theta : FIv_NativeValue.Canon (toQ c.theta)
 mu : FIv_NativeValue.Canon (toQ c.mu)
/-- Actual delivered child packet, not NLI's stronger proposed RowSpec256. -/
def Packet (pub : Public) (claims : NLC_Finish.Claims) (alpha : NLC_Finish.Alpha)
 (c : r1_wire.Challenges) : Prop :=
 ∃ result events,
 NLH_RustCuts.Cuts
  (NLH_WrapperState.step (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c))
  NLH_WrapperState.order (NLH_WrapperRoot.initial (toPublic pub)) result events ∧
 events <+: NLH_WrapperState.order ∧ NLH_WrapperRoot.Canonical result ∧
 NLH_WrapperRoot.projected result=
  FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
   (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c) ∧
 NLH_WrapperRoot.reference (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c)=
  FIq_Native.pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
   (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha) (toChallenges c)
/-- SAME arguments are substituted forward into the actual child theorem.
This is an intermediate domain lemma, not a136 row root or native carrier. -/
theorem install (pub : Public) (claims : NLC_Finish.Claims) (alpha : NLC_Finish.Alpha)
 (c : r1_wire.Challenges) (domain : InputDomain pub c)
 (hc : ∀ row∈(mapArray (mapArray toQ) claims).val,FIw_ArrayValue.canonical row)
 (ha : FIw_ArrayValue.canonical (mapArray toQ alpha)) : Packet pub claims alpha c := by
 exact NLH_WrapperRoot.source (toPublic pub) (mapArray (mapArray toQ) claims) (mapArray toQ alpha)
  (toChallenges c) domain.digest hc ha domain.zc domain.lambda domain.chi domain.theta domain.mu domain.asset
#print axioms install
set_option pp.proofs false in #print install
end AspisR1.NLU_Terminal
end
