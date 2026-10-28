import R1Z.PV_RDEAC_NameValue
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_NameSimulation
open PV_RDB1_V183_ReserveWorld PV_RDEAC_AppendSimulation PV_CBL_StringBytesAdapter
open PV_RDEAC_NameText
variable [ExternalTypes]

/-- Complete source name stage at its physical buffer representation. The
constructor is not assumed successful here; this lemma is applied only to its
returning arm. Each of the actual 65 appends is identified by NameValue and the
physical fill theorem; allocator, frame, address and capacity are retained. -/
theorem complete {S F : Type} (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (shape : Shape)
    (digest : Array U8 32#usize) (s : String) (b : Buffer U8) (w : World S F)
    (repr : Represents s b) (fits : b.values.length+69≤b.capacity)
    (cap : b.capacity≤Usize.max) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    ∃ out after,
      PV_RDEA_NameFill.fill step shape (digest.val.map PV_RDEAC_NibbleModel.byte) b w=(.ok out,after) ∧
      aspis_prover.state_only_entropy.reservation_name digest s 0#usize=ok (s++basenameText digest.val) ∧
      Represents (s++basenameText digest.val) out ∧
      out.address=b.address ∧ out.capacity=b.capacity ∧
      after.allocator=w.allocator ∧ after.history=w.history ∧ after.frame=w.frame := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  have length : digest.val.length=32 := digest.property
  have fillFits : b.values.length+2*(digest.val.map PV_RDEAC_NibbleModel.byte).length+5≤b.capacity := by
    rw [List.length_map,length]
    omega
  obtain ⟨out,after,run,hcap,hval,haddr,halloc,hhist,hframe⟩ :=
    PV_RDEA_NameFill.complete step shape _ b w fillFits
  refine ⟨out,after,run,?_,?_,haddr,hcap,halloc,hhist,hframe⟩
  · apply PV_RDEAC_NameValue.start ops digest s
    change b.values=encodeList s at repr
    rw [←repr]
    omega
  · change out.values=encodeList (s++basenameText digest.val)
    rw [hval,PV_RDEAC_AppendSimulation.encode_append,←name_bytes,←repr]

#print axioms complete
end R1Z.PV_RDEAC_NameSimulation
