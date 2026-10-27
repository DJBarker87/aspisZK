import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.PV_CB_Op105Funs
import R1Z.PV_CB_Op109Funs
import R1Z.ProverRwP7CurrentFieldSource
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
namespace PV_D188_Clone1Eval
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


def host_semantic.clone_semantic_columns_loop1.body
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (i : Std.Usize) :
  Result (ControlFlow ((Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) ×
    Std.Usize) (Array (alloc.vec.Vec aspis_core.field.M31) 26#usize))
  := do
  if i < 26#usize
  then
    let i1 ← Aeneas.Std.lift (Std.Usize.wrapping_sub i 16#usize)
    let v ← Array.index_usize mask_only i1
    let v1 ←
      alloc.vec.CloneVec.clone aspis_core.field.M31.Insts.CoreCloneClone v
    massert (i < 26#usize)
    let (v2, index_mut_back) ← Array.index_mut_usize c1 i
    let c11 := index_mut_back v2
    let c12 ← Array.update c11 i v1
    let i2 ← Aeneas.Std.lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (c12, i2))
  else ok (done c1)

def host_semantic.clone_semantic_columns_loop1
  (mask_only : Array (alloc.vec.Vec aspis_core.field.M31) 10#usize)
  (c1 : Array (alloc.vec.Vec aspis_core.field.M31) 26#usize) (i : Std.Usize) :
  Result (Array (alloc.vec.Vec aspis_core.field.M31) 26#usize)
  := do
  loop
    (fun (c11, i1) => host_semantic.clone_semantic_columns_loop1.body mask_only
      c11 i1)
    (c1, i)
#eval (do
 let s ← lift (Array.to_slice (Array.make 1#usize [7#u32]))
 let z ← lift (Array.to_slice (Array.make 1#usize [0#u32]))
 let v ← host_semantic.clone_semantic_columns_loop1 (Array.repeat 10#usize (vec s)) (Array.repeat 26#usize (vec z)) 16#usize
 ok (v.val.map (fun a => a.val.map (fun x => x.val))) : Result (List (List Nat)))
end PV_D188_Clone1Eval
