import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_AccumulateEval
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

def host_sumcheck.interpolation_accumulate_loop.body
  (basis : Array aspis_core.field.M31 28#usize) (scale : aspis_core.field.QM31)
  (out : Array aspis_core.field.QM31 28#usize) (k : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 28#usize) × Std.Usize)
    (Array aspis_core.field.QM31 28#usize))
  := do
  if k < 28#usize
  then
    let value ← Array.index_usize out k
    let m ← Array.index_usize basis k
    let delta ← aspis_core.field.QM31.mul_m31 scale m
    let next ← aspis_core.field.QM31.add value delta
    let out1 ← Array.update out k next
    let k1 ← Aeneas.Std.lift (Std.Usize.wrapping_add k 1#usize)
    ok (cont (out1, k1))
  else ok (done out)

def host_sumcheck.interpolation_accumulate_loop
  (out : Array aspis_core.field.QM31 28#usize)
  (basis : Array aspis_core.field.M31 28#usize) (scale : aspis_core.field.QM31)
  (k : Std.Usize) :
  Result (Array aspis_core.field.QM31 28#usize)
  := do
  loop
    (fun (out1, k1) => host_sumcheck.interpolation_accumulate_loop.body basis
      scale out1 k1)
    (out, k)

def host_sumcheck.interpolation_accumulate
  (out : Array aspis_core.field.QM31 28#usize)
  (basis : Array aspis_core.field.M31 28#usize) (scale : aspis_core.field.QM31)
  :
  Result (Array aspis_core.field.QM31 28#usize)
  := do
  host_sumcheck.interpolation_accumulate_loop out basis scale 0#usize
#eval (do let one ← aspis_core.field.QM31.ONE
          let scale := {one with c0 := {one.c0 with a:=3#u32}}
          let a ← host_sumcheck.interpolation_accumulate (Array.repeat 28#usize one) (Array.repeat 28#usize 2#u32) scale
          ok (a.val.map (fun q => q.c0.a.val)) : Result (List Nat))
end PV_D188_AccumulateEval
