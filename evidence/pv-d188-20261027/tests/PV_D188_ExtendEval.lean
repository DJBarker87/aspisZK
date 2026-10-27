import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_ExtendEval
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

def host_sumcheck.interpolation_shift
  (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) :
  Result aspis_core.field.M31
  := do
  if k = 0#usize
  then aspis_core.field.M31.ZERO
  else
    let i ← Aeneas.Std.lift (Std.Usize.wrapping_sub k 1#usize)
    Array.index_usize basis i

def host_sumcheck.interpolation_basis_cell
  (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize) (j : Std.Usize)
  :
  Result (Array aspis_core.field.M31 28#usize)
  := do
  let shifted ← host_sumcheck.interpolation_shift basis k
  let m ← Array.index_usize basis k
  let i ← Aeneas.Std.lift (UScalar.cast .U32 j)
  let m1 ← aspis_core.field.M31.mul m i
  let next ← aspis_core.field.M31.sub shifted m1
  Array.update basis k next

def host_sumcheck.interpolation_extend_loop.body
  (j : Std.Usize) (basis : Array aspis_core.field.M31 28#usize) (k : Std.Usize)
  :
  Result (ControlFlow ((Array aspis_core.field.M31 28#usize) × Std.Usize)
    (Array aspis_core.field.M31 28#usize))
  := do
  if k > 0#usize
  then
    let k1 ← Aeneas.Std.lift (Std.Usize.wrapping_sub k 1#usize)
    let basis1 ← host_sumcheck.interpolation_basis_cell basis k1 j
    ok (cont (basis1, k1))
  else ok (done basis)

def host_sumcheck.interpolation_extend_loop
  (basis : Array aspis_core.field.M31 28#usize) (j : Std.Usize) (k : Std.Usize)
  :
  Result (Array aspis_core.field.M31 28#usize)
  := do
  loop
    (fun (basis1, k1) => host_sumcheck.interpolation_extend_loop.body j basis1
      k1)
    (basis, k)

def host_sumcheck.interpolation_extend
  (basis : Array aspis_core.field.M31 28#usize) (degree : Std.Usize)
  (j : Std.Usize) :
  Result (Array aspis_core.field.M31 28#usize)
  := do
  let k ← Aeneas.Std.lift (Std.Usize.wrapping_add degree 2#usize)
  host_sumcheck.interpolation_extend_loop basis j k
#eval (do let a ← host_sumcheck.interpolation_extend (Array.repeat 28#usize 2#u32) 1#usize 3#usize
          ok (a.val.map (fun q => q.val)) : Result (List Nat))
end PV_D188_ExtendEval
