import R1Z.PV_RDEAC_Axioms
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_EndpointReplay
open PV_RDEAC_EndpointInstance (endpoint)
open PV_RDB1_V183_ReserveWorld PV_CBL_StringBytesAdapter PV_CBL_CallbackBundle
open PV_RDEAC_NameText PV_RDEAC_PublishedTail PV_RDEAC_JoinValue

theorem physical {S F R : Type} (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
    (self : @PV_RDEA_ActualReservationTail.Store (AppendTypes base)) (digest : Array U8 32#usize)
    (step : Request → S → Option Nat × S) (free : Nat → Nat → Nat → S → S)
    (shape : Shape) (width : shape.width=1) (nameAddress joinAddress : Nat) (w : World S F)
    (oom : core.alloc.layout.Layout → World S F → R) (panic : World S F → R)
    (next : List U8 → World S F → R) :
    let e := PV_RDB1_V181.deployed step 18446744073709551615 9223372036854775807 shape nameAddress 69 w
    let nameRun := PV_RDEA_ReservationExecution.run step shape nameAddress (digest.val.map PV_RDEAC_NibbleModel.byte) w
    (match e.returned with
     | .error (.allocError layout) => endpoint base self digest step free shape nameAddress joinAddress w oom panic next=oom layout e.world
     | .error .capacityOverflow => endpoint base self digest step free shape nameAddress joinAddress w oom panic next=panic e.world
     | .ok () => ∃ nameBuffer after,
       nameRun=(.ok nameBuffer,after) ∧ nameBuffer.values=encodeList (basenameText digest.val) ∧ nameBuffer.capacity=69 ∧
       after.frame=e.world.frame ∧ after.history=e.world.history ∧
       endpoint base self digest step free shape nameAddress joinAddress w oom panic next=
         PV_RDEAC_JoinHandlers.consume free nameBuffer
          (PV_RDEAC_FullJoin.join step shape joinAddress false
            (needsSeparator (encodeList (directory base self))) (encodeList (directory base self)) nameBuffer.values after) oom panic next) ∧
    PV_RDEA_CapacityEndpoint.sizes nameRun.2.history=PV_RDEA_CapacityEndpoint.sizes w.history++[(0,69,1)] := by
  exact PV_RDEAC_EndpointInstance.complete base ops self digest step free shape width nameAddress joinAddress w oom panic next

#print axioms physical

theorem owned {S F R : Type} (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
    (self : @PV_RDEA_ActualReservationTail.Store (AppendTypes base)) (digest : Array U8 32#usize)
    (step : Request → S → Option Nat × S) (free : Nat → Nat → Nat → S → S)
    (nameBuffer : Buffer U8) (shape : Shape) (width : shape.width=1) (joinAddress : Nat)
    (w : World S F) (abi : 9223372036854775808≤Usize.max)
    (repr : nameBuffer.values=encodeList (basenameText digest.val))
    (oom : core.alloc.layout.Layout → World S F → R) (panic : World S F → R)
    (next : List U8 → World S F → R) :
    letI : ExternalTypes := AppendTypes base
    letI : ExternalFuns := selectedJoin base ops
    let e := PV_RDEAC_FullJoin.join step shape joinAddress false
      (needsSeparator (encodeList (directory base self))) (encodeList (directory base self)) nameBuffer.values w
    PV_RDEAC_JoinHandlers.consume free nameBuffer e oom panic next=
      (match e.returned with
       | .error (.allocError layout) => oom layout e.world
       | .error .capacityOverflow => panic (PV_RDEAC_OwnedCleanup.release free nameBuffer (PV_RDEAC_OwnedCleanup.release free e.buffer e.world))
       | .ok () => next (encodeList (PV_RDEAC_JoinString.joinedText (directory base self) (basenameText digest.val)))
          (PV_RDEAC_OwnedCleanup.release free nameBuffer e.world)) ∧
    (e.returned=.ok () → PV_RDEA_ActualEndpointConsumer.afterCapacity self digest ""=
      ok (PV_RDEAC_JoinString.joinedText (directory base self) (basenameText digest.val))) ∧
    PV_RDEA_PrefixWords.Prefix (PV_RDEA_CapacityEndpoint.sizes (PV_RDEAC_JoinHandlers.finalWorld free nameBuffer e).history)
      (PV_RDEA_CapacityEndpoint.sizes w.history++PV_RDEA_PathSchedule.joinWord
        (encodeList (directory base self)).length nameBuffer.values.length false
        (needsSeparator (encodeList (directory base self)))) := by
  exact PV_RDEAC_EndpointInstance.owned base ops self digest step free nameBuffer shape width joinAddress w abi repr oom panic next

#print axioms owned

theorem source_tail (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
    (self : @PV_RDEA_ActualReservationTail.Store (AppendTypes base)) (digest : Array U8 32#usize)
    {S F : Type} (step : Request → S → Option Nat × S)
    (shape : Shape) (width : shape.width=1) (address : Nat) (w : World S F)
    (target : System.Platform.numBits=64)
    (success : (PV_RDEAC_FullJoin.join step shape address false
      (needsSeparator (encodeList (directory base self)))
      (encodeList (directory base self)) (encodeList (basenameText digest.val)) w).returned=.ok ()) :
    letI : ExternalTypes := AppendTypes base
    letI : ExternalFuns := selectedJoin base ops
    PV_RDEA_ActualReservationTail.tail self digest=
      ok (PV_RDEAC_JoinString.joinedText (directory base self) (basenameText digest.val)) := by
  exact PV_RDEAC_SourceTail.tail base ops self digest step shape width address w target success

#print axioms source_tail

theorem source_factor (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
    (self : @PV_RDEA_ActualReservationTail.Store (AppendTypes base)) (nonce : Array U8 32#usize) :
    letI : ExternalTypes := AppendTypes base
    letI : ExternalFuns := selectedJoin base ops
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path self nonce=(do
      let digest ← PV_RDEA_ActualReservationTail.prelude self nonce
      PV_RDEA_ActualReservationTail.tail self digest) := by
  exact PV_RDEAC_SourceTail.source_factor base ops self nonce

#print axioms source_factor

end R1Z.PV_RDEAC_EndpointReplay
