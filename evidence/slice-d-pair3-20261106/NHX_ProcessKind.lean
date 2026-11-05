import NHM_ByteProducts
import NHI_Scalar
import NHM_RegularDomain
set_option autoImplicit false
noncomputable section
namespace NHX_ProcessKind
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues FIo_Native
variable [FIo_Native.Allocation]
def reference
  (w : _root_.FIo_Native.weights.Weights) (kind : Std.Usize)
  (alpha : Slice aspis_core.field.wide_exact.WideExact) (f : Slice Std.U8)
  (folds : Std.Usize) (n : Std.Usize)
  (ap0 : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (ap1 : Array aspis_core.field.wide_exact.WideExact 4#usize)
  (scratch : alloc.vec.Vec aspis_core.field.QM31)
  (parts : Array aspis_core.field.wide_exact.WideExact 7#usize) :
  Result ((core.result.Result Unit verifier.Error) × (alloc.vec.Vec
    aspis_core.field.QM31) × (Array aspis_core.field.wide_exact.WideExact
    7#usize))
  := do
 let k ←
   if kind < 4#usize
   then ok (Std.Usize.wrapping_sub kind 1#usize)
   else ok (Std.Usize.wrapping_sub kind 2#usize)
 let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut scratch)
 let s1 ← _root_.FIo_Native.weights.Weights.tensor w k folds s
 let a ← Array.index_usize w.factors k
 let a1 ← Array.index_usize a 0#usize
 let scale ← FIo_Native.weights.Weights.scalar_factor a1 ap0
 let (scratch1, scale1) ←
   if folds = 2#usize
   then
     do
     let a2 ← Array.index_usize a 1#usize
     let we ← FIo_Native.weights.Weights.scalar_factor a2 ap1
     let scale2 ← aspis_core.field.wide_exact.WideExact.mul scale we
     let scratch2 := deref_mut_back s1
     ok (scratch2, scale2)
   else let scratch2 := deref_mut_back s1
        ok (scratch2, scale)
 let pair ← fast_pairing.EbyKDot.new
 let s2 := alloc.vec.Vec.deref scratch1
 let (r, pair1) ← NHM_ByteProducts.reference f s2 pair n
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue _ =>
   let we ← fast_pairing.EbyKDot.finish pair1
   let we1 ← aspis_core.field.wide_exact.WideExact.mul scale1 we
   let parts1 ← Array.update parts kind we1
   ok (core.result.Result.Ok (), scratch1, parts1)
 | core.ops.control_flow.ControlFlow.Break residual =>
   let r1 ←
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       Unit (core.convert.FromSame verifier.Error) residual
   ok (r1, scratch1, parts)

theorem source (w : FIo_Native.weights.Weights) (kind : Usize) (alpha : Slice NE) (f : Slice U8)
 (folds n : Usize) (ap0 ap1 : Array NE 4#usize) (scratch : alloc.vec.Vec NQ)
 (parts : Array NE 7#usize) (s2 : w.variant=FIo_Native.transport.Variant.S2) :
 FIo_Native.weights.process_kind w kind alpha f folds n ap0 ap1 scratch parts=
 reference w kind alpha f folds n ap0 ap1 scratch parts := by
 have cmp:FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant FIo_Native.transport.Variant.D=ok false:=by
  rw [s2];simp [FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,FIo_Native.transport.Variant.read_discriminant]
 unfold FIo_Native.weights.process_kind reference
 rw [cmp]
 simp only [bind_tc_ok,Bool.false_eq_true,ite_false,NHM_ByteProducts.cohort]
 rfl

#print axioms source
end NHX_ProcessKind
end
