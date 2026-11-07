import NMS_RSLGetterLink
import NHJ_DataPacket
import NMS_CloneReference
import NMS_Interpreted
set_option autoImplicit false
noncomputable section
namespace NMS_RSLGetterContract
open Aeneas Aeneas.Std AdapterRw NMS_RSLPoolCarriers
/-- The proposed canonical carrier clause is exactly sufficient for the
CLOSED getter's ACTUAL native clone domain; no String variant is renamed or
classified as a scalar error. -/
theorem native_domain (a : r1_pool_adapter.owned.OwnedAccount)
 (safe : NMS_CloneReference.SnapshotErrors (account a)) :
 ∀ e, a.bytes = .Err e → NGL_CloneDomain.SnapshotError e := by
 intro e stored
 have image : (account a).bytes = .error (NMS_RSLError.error e) := by
   simp only [account,stored,NMS_RSLError.reply]
 rcases safe _ image with same | same
 · left
   have h := congrArg NMS_RSLError.raw same
   rw [NMS_RSLError.left] at h
   exact h
 · right
   have h := congrArg NMS_RSLError.raw same
   rw [NMS_RSLError.left] at h
   exact h

/-- Apply the CLOSED TX2:229 packet at SAME original account, with its full
recorded domain discharged above. This is an actual child installation, not
a new endpoint hypothesis. -/
theorem closed (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (safe : NMS_CloneReference.SnapshotErrors (account a)) :
 NMS_Emitted.get (NGL_CloneDomain.install ops) a =
 .ok (NHJ_DataPacket.G a (NHJ_DataPacket.childReply a)) := by
 rw [NMS_EmittedLinks.getter]
 exact NHJ_DataPacket.substitute ops a (native_domain a safe)

/-- Its canonical returning Result preserves all bytes and the exact error. -/
theorem full_reply (ops : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
 (safe : NMS_CloneReference.SnapshotErrors (account a)) :
 NMS_Interpreted.Simulates (NMS_RSLError.reply NMS_RSLScalars.bytes)
  (NMS_Interpreted.liftResult (NMS_Emitted.get (NGL_CloneDomain.install ops) a))
  (RSL.RS.ofExcept (account a).data) := by
 rw [NMS_EmittedLinks.getter,NGL_CloneDomain.data_result]
 cases stored : a.bytes with
 | Ok v =>
   intro env observation run
   subst observation
   simp only [RSL.RS.ofExcept,RSL.OwnedAccount.data,account,stored,NMS_RSLError.reply]
   rfl
 | Err e =>
   intro env observation run
   subst observation
   simp only [RSL.RS.ofExcept,RSL.OwnedAccount.data,account,stored,NMS_RSLError.reply]
   rfl
#print axioms native_domain
#print axioms closed
#print axioms full_reply
end NMS_RSLGetterContract
