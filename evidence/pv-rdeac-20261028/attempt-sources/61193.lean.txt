import R1Z.PV_RDEAC_ABI
import R1Z.PV_RDEAC_LiteralDomain
import R1Z.PV_RDEAC_FreeWord
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_SourceTail
open PV_RDB1_V183_ReserveWorld PV_CBL_CallbackBundle PV_CBL_StringBytesAdapter
open PV_RDEAC_NameText PV_RDEAC_PublishedTail PV_RDEAC_JoinValue

theorem constructor_callback (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base)) :
    @ExternalFuns.op30 (AppendTypes base) (selectedJoin base ops) 69#usize=ok "" := by
  change PV_CBL_CapacityValue.reference 69#usize=ok ""
  exact PV_CBL_CapacityValue.value _

/-- Source value agreement on native returning executions, alongside the
separate complete physical error laws. Native failures are never promoted to
returning executions of this value dictionary. -/
theorem tail (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
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
  letI : ExternalTypes := AppendTypes base
  letI : ExternalFuns := selectedJoin base ops
  rw [PV_RDEA_ActualEndpointConsumer.capacity_consumer,constructor_callback]
  simp only [bind_tc_ok]
  exact (PV_RDEAC_JoinSimulation.returning base ops self digest step shape width address w
    (PV_RDEAC_ABI.word_room target) success).1

theorem source_factor (base : ExternalTypes) (ops : @ExternalFuns (AppendTypes base))
    (self : @PV_RDEA_ActualReservationTail.Store (AppendTypes base)) (nonce : Array U8 32#usize) :
    letI : ExternalTypes := AppendTypes base
    letI : ExternalFuns := selectedJoin base ops
    aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.reservation_path self nonce=(do
      let digest ← PV_RDEA_ActualReservationTail.prelude self nonce
      PV_RDEA_ActualReservationTail.tail self digest) := by
  letI : ExternalTypes := AppendTypes base
  letI : ExternalFuns := selectedJoin base ops
  exact PV_RDEA_ActualReservationTail.source_factor self nonce

#print axioms constructor_callback
#print axioms tail
#print axioms source_factor
end R1Z.PV_RDEAC_SourceTail
