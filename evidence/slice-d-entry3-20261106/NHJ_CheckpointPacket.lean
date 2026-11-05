import NHJ_LengthPacket
import NGL_CheckpointModel
set_option autoImplicit false
noncomputable section
namespace NHJ_CheckpointPacket
open Aeneas Aeneas.Std Result
attribute [local instance] Classical.propDecidable
abbrev A := NGL_CloneDomain.Account
abbrev PE := NGL_CloneDomain.PE
abbrev K := NGL_ReadonlyModel.Key
structure Reply where
  success : Bool
  value : Usize
  borrow : Bool

def decode (r : Reply) : core.result.Result Usize PE :=
  if r.success then .Ok r.value else .Err (NHJ_DataPacket.errorReply r.borrow)
def encode : core.result.Result Usize PE → Reply
  | .Ok n => ⟨true,n,false⟩
  | .Err e => ⟨false,0#usize,NHJ_DataPacket.encodeError e⟩
theorem decode_encode (r : core.result.Result Usize PE) (domain : NGL_LengthCarrier.domain r) :
    decode (encode r) = r := by
  rcases domain with ⟨n,rfl⟩ | rfl | rfl <;> rfl

def G (a : A) (program : K) (writable : Bool) (r : Reply) : core.result.Result Unit PE :=
  if (!(decide (a.owner = program))) || a.is_signer || a.executable || (a.is_writable != writable)
  then .Err .InvalidAccountData
  else match decode r with
  | .Err e => .Err e
  | .Ok n => if n != 1768#usize then .Err .InvalidAccountData else .Ok ()

theorem substitute (ops : AdapterRw.Ops) (a : A) (program : K) (writable : Bool)
    (domain : NGL_LengthCarrier.domain a.length) :
    AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
      (NGL_CheckpointModel.install ops) a program writable =
      ok (G a program writable (encode a.length)) := by
  rw [NGL_CheckpointModel.result]
  unfold G
  rw [decode_encode a.length domain]
  rfl
#print axioms decode_encode
#print axioms substitute
end NHJ_CheckpointPacket
