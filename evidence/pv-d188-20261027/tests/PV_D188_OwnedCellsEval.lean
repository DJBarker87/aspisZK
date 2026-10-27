import Aeneas
import R1Z.ProverRwFullTypes
import R1Z.ProverRwP7CurrentFieldSource

import R1Z.PV_CB_Op105Funs
import R1Z.PV_CB_Op109Funs
open Aeneas Aeneas.Std Result ProverRwFull R1Z
namespace PV_CB_OwnedEncoder
def owned.basis_cell
  {E : Type} (aspis_corer0scalarCodeFieldInst : aspis_core.r0.scalar.CodeField
  E) (out : Array E 512#usize) (width : Std.Usize) (j : Std.Usize) (factor : E)
  :
  Result (Array E 512#usize)
  := do
  let t ← Array.index_usize out j
  let t1 ← aspis_corer0scalarCodeFieldInst.mul t factor
  let i ← lift (Std.Usize.wrapping_add width j)
  Array.update out i t1


end PV_CB_OwnedEncoder
namespace R1Z.PV_CB_OwnedMask
def owned.cell
  (out : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize) (index : Std.Usize)
  (value : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) :
  Result (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize)
  := do
  Array.update out index value


end R1Z.PV_CB_OwnedMask
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
#eval (do
 let v ← PV_CB_OwnedEncoder.owned.basis_cell mfield (Array.repeat 512#usize 2#u32) 1#usize 0#usize 3#u32
 let out ← Array.index_usize v 1#usize
 ok out.val : Result Nat)
#eval (do
 let z := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
 let q := ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE
 let v ← R1Z.PV_CB_OwnedMask.owned.cell (Array.repeat 27#usize z) 5#usize q
 let out ← Array.index_usize v 5#usize
 ok [out.c0.a.val,out.c0.b.val,out.c1.a.val,out.c1.b.val] : Result (List Nat))
