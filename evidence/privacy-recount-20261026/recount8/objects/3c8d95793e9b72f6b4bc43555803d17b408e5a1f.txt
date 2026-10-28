import R1Z.PV_RDEAC_NameSimulation
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEAC_AfterCapacity
open PV_RDB1_V183_ReserveWorld PV_RDEAC_AppendSimulation PV_CBL_StringBytesAdapter
open PV_RDEAC_NameText
variable [ExternalTypes]

noncomputable def joinTail (ops : ExternalFuns) (self : PV_RDEA_ActualReservationTail.Store)
    (s : String) : Result std.path.PathBuf :=
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  do
    let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
    std.path.Path.join alloc.string.String.Insts.CoreConvertAsRefPath p s

theorem source (ops : ExternalFuns) (self : PV_RDEA_ActualReservationTail.Store)
    (digest : Array U8 32#usize) (s : String)
    (bound : (encodeList s).length+69≤Usize.max) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    PV_RDEA_ActualEndpointConsumer.afterCapacity self digest s=
      joinTail ops self (s++basenameText digest.val) := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  unfold PV_RDEA_ActualEndpointConsumer.afterCapacity
  rw [PV_RDEAC_NameValue.start ops digest s bound]
  rfl

/-- Concrete connection from afterCapacity to the physical name stage and
actual op25/op26 tail. No arbitrary continuation equation is assumed. -/
theorem simulation {S F : Type} (ops : ExternalFuns)
    (step : Request → S → Option Nat × S) (shape : Shape)
    (self : PV_RDEA_ActualReservationTail.Store) (digest : Array U8 32#usize)
    (s : String) (b : Buffer U8) (w : World S F)
    (repr : Represents s b) (fits : b.values.length+69≤b.capacity)
    (cap : b.capacity≤Usize.max) :
    letI : ExternalFuns := PV_CBL_AppendSource.selected ops
    ∃ out after,
      PV_RDEA_NameFill.fill step shape (digest.val.map PV_RDEAC_NibbleModel.byte) b w=(.ok out,after) ∧
      PV_RDEA_ActualEndpointConsumer.afterCapacity self digest s=joinTail ops self (s++basenameText digest.val) ∧
      Represents (s++basenameText digest.val) out ∧
      out.address=b.address ∧ out.capacity=b.capacity ∧
      after.allocator=w.allocator ∧ after.history=w.history ∧ after.frame=w.frame := by
  letI : ExternalFuns := PV_CBL_AppendSource.selected ops
  obtain ⟨out,after,run,_,rep,haddr,hcap,halloc,hhist,hframe⟩ :=
    PV_RDEAC_NameSimulation.complete ops step shape digest s b w repr fits cap
  refine ⟨out,after,run,source ops self digest s ?_,rep,haddr,hcap,halloc,hhist,hframe⟩
  change b.values=encodeList s at repr
  rw [←repr]
  omega

#print axioms source
#print axioms simulation
end R1Z.PV_RDEAC_AfterCapacity
