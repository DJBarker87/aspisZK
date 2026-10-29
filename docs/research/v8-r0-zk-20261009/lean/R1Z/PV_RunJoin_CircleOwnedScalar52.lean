import R1Z.PV_AL_CircleOwnedFuns
import R1Z.PV_RunJoin_CircleRawScalar52
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleOwnedScalar52
abbrev O := PV_AL_CircleOwned.aspis_core.field.M31

theorem f0 :
    PV_AL_CircleOwned.aspis_core.field.P = PV_RunJoin_CircleRawScalar52.field.P  := by
  unfold PV_AL_CircleOwned.aspis_core.field.P PV_RunJoin_CircleRawScalar52.field.P
  rfl

theorem f1 (x : Std.U32) :
    PV_AL_CircleOwned.aspis_core.field.ct.subtract_p x= PV_RunJoin_CircleRawScalar52.field.ct.subtract_p x := by
  unfold PV_AL_CircleOwned.aspis_core.field.ct.subtract_p PV_RunJoin_CircleRawScalar52.field.ct.subtract_p
  simp only [f0]

theorem f2 (x : Std.U64) :
    PV_AL_CircleOwned.aspis_core.field.ct.reduce64 x= PV_RunJoin_CircleRawScalar52.field.ct.reduce64 x := by
  unfold PV_AL_CircleOwned.aspis_core.field.ct.reduce64 PV_RunJoin_CircleRawScalar52.field.ct.reduce64
  simp only [f0,f1]

theorem f3 (a : Std.U32) (b : Std.U32) :
    PV_AL_CircleOwned.aspis_core.field.ct.add a b= PV_RunJoin_CircleRawScalar52.field.ct.add a b := by
  unfold PV_AL_CircleOwned.aspis_core.field.ct.add PV_RunJoin_CircleRawScalar52.field.ct.add
  simp only [f1]

theorem f4 (a : Std.U32) (b : Std.U32) :
    PV_AL_CircleOwned.aspis_core.field.ct.sub a b= PV_RunJoin_CircleRawScalar52.field.ct.sub a b := by
  unfold PV_AL_CircleOwned.aspis_core.field.ct.sub PV_RunJoin_CircleRawScalar52.field.ct.sub
  simp only [f0,f1]

theorem f5 (a : Std.U32) :
    PV_AL_CircleOwned.aspis_core.field.ct.neg a= PV_RunJoin_CircleRawScalar52.field.ct.neg a := by
  unfold PV_AL_CircleOwned.aspis_core.field.ct.neg PV_RunJoin_CircleRawScalar52.field.ct.neg
  simp only [f0]

theorem f6 (a : Std.U32) :
    PV_AL_CircleOwned.aspis_core.field.ct.is_zero a= PV_RunJoin_CircleRawScalar52.field.ct.is_zero a := by
  unfold PV_AL_CircleOwned.aspis_core.field.ct.is_zero PV_RunJoin_CircleRawScalar52.field.ct.is_zero
  rfl

theorem f7 (self : O) (other : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq self other= PV_RunJoin_CircleRawScalar52.field.M31.Insts.CoreCmpPartialEqM31.eq self other := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq PV_RunJoin_CircleRawScalar52.field.M31.Insts.CoreCmpPartialEqM31.eq
  rfl

theorem f8 (x : Std.U64) :
    PV_AL_CircleOwned.aspis_core.field.reduce_u64 x= PV_RunJoin_CircleRawScalar52.field.reduce_u64 x := by
  unfold PV_AL_CircleOwned.aspis_core.field.reduce_u64 PV_RunJoin_CircleRawScalar52.field.reduce_u64
  simp only [f2]

theorem f9 (self : O) (rhs : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.mul self rhs= PV_RunJoin_CircleRawScalar52.field.M31.mul self rhs := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.mul PV_RunJoin_CircleRawScalar52.field.M31.mul
  simp only [f8]

theorem f10 (iter : core.ops.range.Range Std.Usize) (value : O) :
    PV_AL_CircleOwned.aspis_core.field.square_n_loop.body iter value= PV_RunJoin_CircleRawScalar52.field.square_n_loop.body iter value := by
  unfold PV_AL_CircleOwned.aspis_core.field.square_n_loop.body PV_RunJoin_CircleRawScalar52.field.square_n_loop.body
  simp only [f9]

theorem f11 (iter : core.ops.range.Range Std.Usize) (value : O) :
    PV_AL_CircleOwned.aspis_core.field.square_n_loop iter value= PV_RunJoin_CircleRawScalar52.field.square_n_loop iter value := by
  unfold PV_AL_CircleOwned.aspis_core.field.square_n_loop PV_RunJoin_CircleRawScalar52.field.square_n_loop
  simp only [f10]

theorem f12 (value : O) (count : Std.Usize) :
    PV_AL_CircleOwned.aspis_core.field.square_n value count= PV_RunJoin_CircleRawScalar52.field.square_n value count := by
  unfold PV_AL_CircleOwned.aspis_core.field.square_n PV_RunJoin_CircleRawScalar52.field.square_n
  simp only [f11]

theorem f13 (value : Std.U64) :
    PV_AL_CircleOwned.aspis_core.field.M31.reduce_u64 value= PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64 value := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.reduce_u64 PV_RunJoin_CircleRawScalar52.field.M31.reduce_u64
  simp only [f8]

theorem f14 (self : O) (rhs : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.add self rhs= PV_RunJoin_CircleRawScalar52.field.M31.add self rhs := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.add PV_RunJoin_CircleRawScalar52.field.M31.add
  simp only [f3]

theorem f15 (self : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.double self= PV_RunJoin_CircleRawScalar52.field.M31.double self := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.double PV_RunJoin_CircleRawScalar52.field.M31.double
  simp only [f14]

theorem f16 (self : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.inv self= PV_RunJoin_CircleRawScalar52.field.M31.inv self := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.inv PV_RunJoin_CircleRawScalar52.field.M31.inv
  simp only [f9,f12]

theorem f17 (self : O) (rhs : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.sub self rhs= PV_RunJoin_CircleRawScalar52.field.M31.sub self rhs := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.sub PV_RunJoin_CircleRawScalar52.field.M31.sub
  simp only [f4]

theorem f18 (self : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.neg self= PV_RunJoin_CircleRawScalar52.field.M31.neg self := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.neg PV_RunJoin_CircleRawScalar52.field.M31.neg
  simp only [f5]

theorem f19 (self : O) :
    PV_AL_CircleOwned.aspis_core.field.M31.is_zero self= PV_RunJoin_CircleRawScalar52.field.M31.is_zero self := by
  unfold PV_AL_CircleOwned.aspis_core.field.M31.is_zero PV_RunJoin_CircleRawScalar52.field.M31.is_zero
  simp only [f6]


#print axioms f0
#print axioms f1
#print axioms f2
#print axioms f3
#print axioms f4
#print axioms f5
#print axioms f6
#print axioms f7
#print axioms f8
#print axioms f9
#print axioms f10
#print axioms f11
#print axioms f12
#print axioms f13
#print axioms f14
#print axioms f15
#print axioms f16
#print axioms f17
#print axioms f18
#print axioms f19
end R1Z.PV_RunJoin_CircleOwnedScalar52
