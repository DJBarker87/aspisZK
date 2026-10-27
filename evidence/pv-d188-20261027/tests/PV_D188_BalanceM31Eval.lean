import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_BalanceM31Eval
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

def aspis_prover.state_only_hiding.inactive_m31_step
  (sum : aspis_core.field.M31) (table : Slice aspis_core.field.M31)
  (dependent : Std.Usize) (active : Array Bool 1024#usize) (row : Std.Usize) :
  Result aspis_core.field.M31
  := do
  let b ← Array.index_usize active row
  if b
  then ok sum
  else
    if row != dependent
    then let m ← Slice.index_usize table row
         aspis_core.field.M31.add sum m
    else ok sum

def aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body
  (table : Slice aspis_core.field.M31) (dependent : Std.Usize)
  (active : Array Bool 1024#usize) (rows : Std.Usize)
  (sum : aspis_core.field.M31) (row : Std.Usize) :
  Result (ControlFlow (aspis_core.field.M31 × Std.Usize) aspis_core.field.M31)
  := do
  if row < rows
  then
    let sum1 ←
      aspis_prover.state_only_hiding.inactive_m31_step sum table dependent
        active row
    let row1 ← Aeneas.Std.lift (Std.Usize.wrapping_add row 1#usize)
    ok (cont (sum1, row1))
  else ok (done sum)

def aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop
  (table : Slice aspis_core.field.M31) (dependent : Std.Usize)
  (active : Array Bool 1024#usize) (rows : Std.Usize)
  (sum : aspis_core.field.M31) (row : Std.Usize) :
  Result aspis_core.field.M31
  := do
  loop
    (fun (sum1, row1) =>
      aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop.body table
      dependent active rows sum1 row1)
    (sum, row)

def aspis_prover.state_only_hiding.sum_m31_copy_inactive
  (table : Slice aspis_core.field.M31) (dependent : Std.Usize)
  (active : Array Bool 1024#usize) :
  Result aspis_core.field.M31
  := do
  let rows ←
    aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS
  let sum ← aspis_core.field.M31.ZERO
  aspis_prover.state_only_hiding.sum_m31_copy_inactive_loop table dependent
    active rows sum 0#usize

def aspis_prover.state_only_hiding.balance_m31_copy_inactive
  (table : Slice aspis_core.field.M31) (dependent : Std.Usize)
  (active : Array Bool 1024#usize) :
  Result ((core.result.Result Unit
    aspis_prover.state_only_hiding.StateOnlyMaskBuildError) × (Slice
    aspis_core.field.M31))
  := do
  let rows ←
    aspis_statement.state_only_poseidon.STATE_ONLY_POSEIDON_TRACE_ROWS
  let i := Slice.len table
  if i != rows
  then
    ok (core.result.Result.Err
      aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape, table)
  else
    let b ← Array.index_usize active dependent
    if b
    then
      ok (core.result.Result.Err
        aspis_prover.state_only_hiding.StateOnlyMaskBuildError.TraceShape,
        table)
    else
      let sum ←
        aspis_prover.state_only_hiding.sum_m31_copy_inactive table dependent
          active
      let m ← aspis_core.field.M31.ZERO
      let value ← aspis_core.field.M31.sub m sum
      let table1 ← Slice.update table dependent value
      ok (core.result.Result.Ok (), table1)
#eval (do
 let z ← aspis_core.field.M31.ONE
 let s ← lift (Array.to_slice (Array.repeat 1024#usize z))
 let (r,s) ← aspis_prover.state_only_hiding.balance_m31_copy_inactive s 3#usize (Array.repeat 1024#usize false)
 let q ← Slice.index_usize s 3#usize
 ok q.val : Result Nat)
end PV_D188_BalanceM31Eval
