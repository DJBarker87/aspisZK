import R1Z.ProverCommitFuelMass22
import R1Z.ProverCommitSimulatorOracle18
/-! Uniform five-word windows of the same finite shared source oracle.
The start is fixed in these statements. A stopping-time/adaptive-start
transport is deliberately not inferred from this marginal window law. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFuelOracle22
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitFuelMass22 ProverCommitSimulatorOracle18 R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable

def window (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (stream : Fin 4) (start : Nat) (room : start+k ≤ 2^64)
    (i : Fin k) : R1Z.RomFiniteBin.Address bound :=
  key (count := 2^64) bound fits seed (attempt,stream,⟨start+i.val,by have hi:=i.isLt;omega⟩)

theorem window_injective (bound : Nat) (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (stream : Fin 4) (start : Nat) (room : start+k ≤ 2^64) :
    Function.Injective (window bound fits seed attempt stream start room) := by
  intro i j same
  have he := key_injective (count := 2^64) (Nat.le_refl _) bound fits seed same
  have hv := congrArg (fun z : Index (2^64) => z.2.2.val) he
  exact Fin.ext (Nat.add_left_cancel hv)

/-- One global retained table, not a fresh oracle for every draw. -/
theorem window_uniform {U : Type} [Fintype U] [Nonempty U]
    (bound : Nat) [Fintype (R1Z.RomFiniteBin.Address bound)]
    (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (stream : Fin 4) (start : Nat) (room : start+k ≤ 2^64) :
    MP (fun table : R1Z.RomFiniteBin.Address bound → U =>
      fun i => table (window bound fits seed attempt stream start room i)) := by
  intro f
  have he := QueryScanIdealHistory.coordinates_uniform (U := U)
    (window bound fits seed attempt stream start room)
    (window_injective bound fits seed attempt stream start room) f
  convert he using 1 <;> apply QueryScanIdealHistory.mean_fintype_transport

theorem window_mass {U : Type} [Fintype U] [Nonempty U] (zero : U)
    (bound : Nat) [Fintype (R1Z.RomFiniteBin.Address bound)]
    (fits : 65 ≤ bound) (seed : OracleAnswer)
    (attempt : Fin 8) (stream : Fin 4) (start : Nat) (room : start+k ≤ 2^64) :
    eventMass (fun table : R1Z.RomFiniteBin.Address bound → U =>
      ∀ i, table (window bound fits seed attempt stream start room i)=zero) =
      1 / (Fintype.card U : ℚ)^k := by
  have hm := window_uniform (U := U) bound fits seed attempt stream start room
    (fun draws => if exhausted zero draws then (1 : ℚ) else 0)
  have hp : eventMass (fun table : R1Z.RomFiniteBin.Address bound → U =>
      ∀ i, table (window bound fits seed attempt stream start room i)=zero) =
      eventMass (exhausted zero) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext r <;> split_ifs <;> rfl
  exact hp.trans (exhaustion_mass zero)

#print axioms window_injective
#print axioms window_uniform
#print axioms window_mass
end R1Z.ProverCommitFuelOracle22
