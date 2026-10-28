import R1Z.PV_RDEA_ActualReservationTail
open Aeneas Aeneas.Std Result ProverRwFull
namespace R1Z.PV_RDEA_ActualEndpointConsumer
variable [ExternalTypes] [ExternalFuns]
open PV_RDEA_ActualReservationTail

def afterCapacity (self : Store) (digest : Array U8 32#usize) (s : String) : Result std.path.PathBuf := do
  let name1 ← aspis_prover.state_only_entropy.reservation_name digest s 0#usize
  let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
  std.path.Path.join alloc.string.String.Insts.CoreConvertAsRefPath p name1

theorem capacity_consumer (self : Store) (digest : Array U8 32#usize) :
    tail self digest = (do let s ← ExternalFuns.op30 69#usize; afterCapacity self digest s) := rfl

theorem finite_consumer (self : Store) (digest : Array U8 32#usize) (s : String) :
    afterCapacity self digest s = (do
      let name1 ← PV_RDEA_ActualNameLoop.finite digest 32 s 0#usize
      let p ← std.path.PathBuf.Insts.CoreOpsDerefDerefPath.deref self.directory
      std.path.Path.join alloc.string.String.Insts.CoreConvertAsRefPath p name1) := by
  unfold afterCapacity
  rw [PV_RDEA_ActualNameFinite.start]

theorem constructor_failure (self : Store) (digest : Array U8 32#usize)
    (err : Error) (failed : ExternalFuns.op30 69#usize=.fail err) :
    tail self digest=.fail err := by
  rw [capacity_consumer,failed]
  rfl

#print axioms capacity_consumer
#print axioms finite_consumer
#print axioms constructor_failure
end R1Z.PV_RDEA_ActualEndpointConsumer
