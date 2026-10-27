import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_AssignmentEval
abbrev aspis_core.field.M31 := ProverRwFull.aspis_core.field.M31
abbrev aspis_core.field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev aspis_prover.state_only_hiding.StateOnlyMaskBuildError := ProverRwFull.aspis_prover.state_only_hiding.StateOnlyMaskBuildError
abbrev aspis_core.field.M31.add := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
abbrev aspis_core.field.M31.sub := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
abbrev aspis_core.field.M31.mul := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
abbrev aspis_core.field.M31.double := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.M31.double
abbrev aspis_core.field.QM31.add := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add
abbrev aspis_core.field.QM31.mul := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul
abbrev aspis_core.field.QM31.mul_m31 := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31
abbrev aspis_core.field.CM31.sub := R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.CM31.sub
def aspis_core.field.M31.ZERO : Result U32 := ok 0#u32
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 := ok R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
def aspis_core.field.QM31.ONE : Result aspis_core.field.QM31 := ok R1Z.ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE
def aspis_core.field.QM31.sub (a b : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
 let c0 ← aspis_core.field.CM31.sub a.c0 b.c0
 let c1 ← aspis_core.field.CM31.sub a.c1 b.c1
 ok {c0,c1}
def aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS : Result Usize := ok 1024#usize
def multiproof.LEAF_BITS : Result U32 := ok 18#u32
def multiproof.MAX_BATCH : Result Usize := ok 16#usize

def host_sumcheck.evaluate_assignment_loop.body
  (round : Std.Usize) (remaining : Std.Usize) (assignment : Std.Usize)
  (at1 : Array aspis_core.field.QM31 10#usize) (offset : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 10#usize) × Std.Usize)
    (Array aspis_core.field.QM31 10#usize))
  := do
  if offset < remaining
  then
    let i ← Aeneas.Std.lift (Std.Usize.wrapping_sub remaining 1#usize)
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_sub i offset)
    let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_shr assignment (UScalar.cast .U32 i1))
    let i3 ← Aeneas.Std.lift (i2 &&& 1#usize)
    let q ←
      if i3 = 0#usize
      then aspis_core.field.QM31.ZERO
      else aspis_core.field.QM31.ONE
    let i4 ← Aeneas.Std.lift (Std.Usize.wrapping_add round 1#usize)
    let i5 ← Aeneas.Std.lift (Std.Usize.wrapping_add i4 offset)
    let at2 ← Array.update at1 i5 q
    let offset1 ← Aeneas.Std.lift (Std.Usize.wrapping_add offset 1#usize)
    ok (cont (at2, offset1))
  else ok (done at1)

def host_sumcheck.evaluate_assignment_loop
  (round : Std.Usize) (remaining : Std.Usize) (assignment : Std.Usize)
  (at1 : Array aspis_core.field.QM31 10#usize) (offset : Std.Usize) :
  Result (Array aspis_core.field.QM31 10#usize)
  := do
  loop
    (fun (at2, offset1) => host_sumcheck.evaluate_assignment_loop.body round
      remaining assignment at2 offset1)
    (at1, offset)
#eval (do let zero ← aspis_core.field.QM31.ZERO
          let a ← host_sumcheck.evaluate_assignment_loop 1#usize 3#usize 5#usize (Array.repeat 10#usize zero) 0#usize
          ok (a.val.map (fun q => q.c0.a.val)) : Result (List Nat))
end PV_D188_AssignmentEval
