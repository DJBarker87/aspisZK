import AspisR1SimulatorCoin18.Funs
/-! One owned simulator coin transition. The P6 source equality is the
sim::simcoin18::coin_transition Kani receipt. This module does not identify
HOST_HASH with uniform coins, prove the nonzero loop, or model programming. -/
set_option autoImplicit false
namespace R1Z.ProverCommitSimulatorCoin18
open Aeneas Aeneas.Std Result
abbrev Bytes32 := Array U8 32#usize
abbrev Hash := Slice (Slice U8) → Result Bytes32

def domain : Slice U8 := Array.to_slice (Array.make 20#usize
  [85#u8, 78#u8, 80#u8, 82#u8, 79#u8, 86#u8, 69#u8, 68#u8, 58#u8, 82#u8,
   49#u8, 58#u8, 83#u8, 73#u8, 77#u8, 58#u8, 67#u8, 79#u8, 73#u8, 78#u8])

def frame (seed : Bytes32) (attempt : U32) (stream : U8) (counter : U64) :
    Slice (Slice U8) :=
  Array.to_slice (Array.make 5#usize [domain, Array.to_slice seed,
    Array.to_slice (core.num.U32.to_le_bytes attempt),
    Array.to_slice (Array.make 1#usize [stream]),
    Array.to_slice (core.num.U64.to_le_bytes counter)])

/-- Exact extracted hash request and release-mode wrapping counter update.
There is exactly one callback, and no fresh coin is silently introduced. -/
theorem extracted_step (hash : Hash) (seed : Bytes32) (attempt : U32)
    (stream : U8) (counter : U64) :
    AspisR1SimulatorCoin18.sim.coin_owned18 hash seed attempt stream counter =
      (do let answer ← hash (frame seed attempt stream counter)
          ok (answer, U64.wrapping_add counter 1#u64)) := by
  rfl

/-- Failed/diverging callback evaluation remains failed/diverging. In the
successful case the only changed source field is the counter. -/
theorem successful_step (hash : Hash) (seed answer : Bytes32) (attempt : U32)
    (stream : U8) (counter : U64)
    (answered : hash (frame seed attempt stream counter) = ok answer) :
    AspisR1SimulatorCoin18.sim.coin_owned18 hash seed attempt stream counter =
      ok (answer, U64.wrapping_add counter 1#u64) := by
  rw [extracted_step, answered]
  rfl

#print axioms extracted_step
#print axioms successful_step
end R1Z.ProverCommitSimulatorCoin18
