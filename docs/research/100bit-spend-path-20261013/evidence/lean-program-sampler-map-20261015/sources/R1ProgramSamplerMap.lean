import FS2.Statement
import AspisV8R19.OracleProgramOps
import R1GenericProgramRenameMass

/-! Sequential sampler views of oracle programs and independent-mean transport
under address renaming. This does not assert follow, first-read, or shared-oracle
INJ preservation. -/
set_option autoImplicit false

namespace AspisR1.ProgramSamplerMap

open AspisV8PairedCommitment
open AspisV8R19 AspisV8R19.MemoizedProgramLaw
open AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling
open AspisV8R19.AdaptiveFirstReadLaw

variable {I J A C : Type}

def fromProgram : Program I A C → FS2.Sampler I A C
  | .done c => .done c
  | .ask i next => .ask i (fun a => fromProgram (next a))

theorem toProgram_fromProgram [DecidableEq I] [Inhabited A]
    (p : Program I A C) : (fromProgram p).toProgram = p := by
  induction p with
  | done c => rfl
  | ask i next ih =>
      simp only [fromProgram, FS2.Sampler.toProgram]
      congr 1
      funext a
      exact ih a

def map [DecidableEq I] [Inhabited A]
    (label : I → J) (s : FS2.Sampler I A C) : FS2.Sampler J A C :=
  fromProgram (OracleProgramOps.rename label s.toProgram)

theorem independentMean_map [DecidableEq I] [DecidableEq J]
    [Inhabited A] [Fintype A]
    (label : I → J) (s : FS2.Sampler I A C) (obs : C → ℚ) :
    independentMean (map label s).toProgram (fun v => obs v.2) =
      independentMean s.toProgram (fun v => obs v.2) := by
  change independentMean
      (fromProgram (OracleProgramOps.rename label s.toProgram)).toProgram
      (fun v => obs v.2) = _
  rw [toProgram_fromProgram]
  calc
    independentMean (OracleProgramOps.rename label s.toProgram)
        (fun v => obs v.2) =
      independentMean s.toProgram (fun v => obs (OracleProgramOps.mapView label v).2) :=
        AspisR1.GenericProgramRenameMass.independentMean_rename label s.toProgram
          (fun v => obs v.2)
    _ = independentMean s.toProgram (fun v => obs v.2) := rfl

#print axioms toProgram_fromProgram
#print axioms independentMean_map

end AspisR1.ProgramSamplerMap
