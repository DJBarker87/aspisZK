import NLB_EventObservation
import NLB_C04Domain
set_option autoImplicit false
noncomputable section
namespace NLB_ErrorTransport
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved
/-- An unchanged prefix supplies its actual returned value and equation to the
next local proof. Off-branch callee domains are never required. -/
theorem observe_bind_entered {A B : Type} (m : NJU_Log.Run Event A)
 (native source : A → NJU_Log.Run Event (core.result.Result B verifier.Error))
 (tail : ∀ a,m.result=ok a → observeCommon (native a)=observeCommon (source a)) :
 observeCommon (m >>= native)=observeCommon (m >>= source) := by
 rcases m with ⟨reply,events⟩
 cases reply with
 | fail error => rfl
 | div => rfl
 | ok value =>
   change (reject (native value).result,(events++(native value).events).map projectEvent)=
    (reject (source value).result,(events++(source value).events).map projectEvent)
   rw [List.map_append,List.map_append]
   exact congrArg (fun x : Result B × List Event => (x.1,events.map projectEvent++x.2)) (tail value rfl)

def MerkleDomain (wr : NP6_StdModel.Reservation) {H : Type}
 (d : aspis_core.digest.Digest32 H) (ck proof pub : Slice U8) (hash : H)
 (proofArg : Slice U8) (p : verifier.Prepared) : Prop :=
 proofArg=proof ∧ ∃ a,NJJ_Common.resume wr d ck proof pub .S2 hash=ok (.Ok (p,a)) ∧
 a.next=10#usize ∧ NID_ResumeFields.Domain p a

theorem split_start (a : verifier.Accumulator)
 (passed : ¬(a.next != NHT_Constants.compact.SPLIT)=true) : a.next=10#usize := by
 have same : a.next=NHT_Constants.compact.SPLIT := by
  apply UScalar.eq_of_val_eq
  simpa using passed
 rw [same]
 unfold NHT_Constants.compact.SPLIT
 rfl
#print axioms observe_bind_entered
#print axioms split_start
end NLB_ErrorTransport
