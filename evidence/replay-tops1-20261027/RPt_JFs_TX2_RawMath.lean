import RPt_JFr_TX2_DotLaneTotal
import RPt_JFs_TX2_FoldLane
import FIo_QRawFuns
set_option autoImplicit false
namespace AspisR1.JFs_TX2_RawMath
open Aeneas Aeneas.Std Result
abbrev extend (x : U32) : U64 := core.convert.num.FromU64U32.from x

theorem mul (a b : U32) : extend a*extend b=ok (UScalar.wrapping_mul (extend a) (extend b)) := by
  apply FIo_ScalarBridge.mul
  rw [JFr_TX2_DotLaneTotal.extend,JFr_TX2_DotLaneTotal.extend]
  have ha:=a.hSize
  have hb:=b.hSize
  norm_num [UScalar.size,U32.size,U32.numBits,U64.size,U64.numBits,UScalarTy.numBits] at ha hb ⊢
  nlinarith

theorem fold (x : U64) :
    FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x=
      ok (FIo_ReduceBounds.fold x) := by
  simp only [FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call,
    FIo_QRaw.canonical.P,lift,bind_tc_ok,JFs_TX2_FoldLane.shift]
  rfl

theorem twice_fold (x : U64) : 2#u64*FIo_ReduceBounds.fold x=
    ok (UScalar.wrapping_mul 2#u64 (FIo_ReduceBounds.fold x)) := by
  apply FIo_ScalarBridge.mul
  have h:=JFs_TX2_FoldLane.fold_bound x
  norm_num [JFs_TX2_FoldLane.R,UScalar.size,U64.size,U64.numBits,UScalarTy.numBits] at h ⊢
  omega

theorem pp : FIo_QRaw.canonical.Q.raw.PP=ok 4611686014132420609#u64 := by
  unfold FIo_QRaw.canonical.Q.raw.PP FIo_QRaw.canonical.P
  rfl

theorem twice_pp : 2#u64*4611686014132420609#u64=ok 9223372028264841218#u64 := by rfl

theorem triple_p : 3#u64*extend FIo_QRaw.canonical.P=ok 6442450941#u64 := by
  unfold FIo_QRaw.canonical.P
  rfl

#print axioms mul
#print axioms fold
#print axioms twice_fold
#print axioms pp
#print axioms twice_pp
#print axioms triple_p
end AspisR1.JFs_TX2_RawMath
