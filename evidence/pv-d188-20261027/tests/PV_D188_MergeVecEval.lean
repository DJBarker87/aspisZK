import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.PV_CB_Op105Funs
import R1Z.PV_CB_Op109Funs
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_MergeVecEval
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

abbrev aspis_core.r0.domain.Point := ProverRwFull.aspis_core.r0.domain.Point
abbrev aspis_core.field.M31.Insts.CoreCloneClone := core.clone.CloneU32
private def vec {T : Type} (s : Slice T) : alloc.vec.Vec T := ⟨s.val,s.property⟩
private def mfield : aspis_core.r0.scalar.CodeField U32 where
 ZERO := ok 0#u32
 ONE := ok 1#u32
 coremarkerCopyInst := core.marker.CopyU32
 corecmpEqInst := core.cmp.EqU32
 from_m31 := fun x => x % 2147483647#u32
 add := ProverRwP7CurrentFieldSource.aspis_core.field.M31.add
 sub := ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub
 neg := PV_CB_ShippedOp109.aspis_core.field.M31.neg
 mul := ProverRwP7CurrentFieldSource.aspis_core.field.M31.mul
 try_inv := PV_CB_ShippedOp105.aspis_core.field.M31.Insts.Aspis_coreR0ScalarCodeField.try_inv


def host_commitment.merge_evaluations_loop.body
  {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (nodes : Slice aspis_core.field.M31) (a : Slice T) (b : Slice T)
  (out : alloc.vec.Vec T) (j : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec T) × Std.Usize) (alloc.vec.Vec T))
  := do
  let i := Slice.len nodes
  if j < i
  then
    let i1 ← j / 2#usize
    let t ← Slice.index_usize a i1
    let m ← Slice.index_usize nodes j
    let t1 ← aspis_corer0scalarCodeFieldInst.from_m31 m
    let t2 ← Slice.index_usize b i1
    let t3 ← aspis_corer0scalarCodeFieldInst.mul t1 t2
    let t4 ← aspis_corer0scalarCodeFieldInst.add t t3
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice T) out j
    let out1 := index_mut_back t4
    let j1 ← Aeneas.Std.lift (Std.Usize.wrapping_add j 1#usize)
    ok (cont (out1, j1))
  else ok (done out)

def host_commitment.merge_evaluations_loop
  {T : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  T) (nodes : Slice aspis_core.field.M31) (a : Slice T) (b : Slice T)
  (out : alloc.vec.Vec T) (j : Std.Usize) :
  Result (alloc.vec.Vec T)
  := do
  loop
    (fun (out1, j1) => host_commitment.merge_evaluations_loop.body
      aspis_corer0scalarCodeFieldInst nodes a b out1 j1)
    (out, j)
#eval (do
 let nodes ← lift (Array.to_slice (Array.make 2#usize [1#u32,2#u32]))
 let a ← lift (Array.to_slice (Array.make 1#usize [3#u32]))
 let b ← lift (Array.to_slice (Array.make 1#usize [4#u32]))
 let z ← lift (Array.to_slice (Array.repeat 2#usize 0#u32))
 let v ← host_commitment.merge_evaluations_loop mfield nodes a b (vec z) 0#usize
 ok (v.val.map (fun x => x.val)) : Result (List Nat))
end PV_D188_MergeVecEval
