import NIG_TailControl
set_option autoImplicit false
noncomputable section
namespace NIG_PairSuffix
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
open NIG_PairFrames
variable [FIo_Native.Allocation]

def dispatch (w:W) (f:Slice U8) (ap0 ap1:Powers) (kappa:NE) (parts:Parts):Result NIG_TailControl.R:=do
 let low←NIG_LowLoop.low_reference ap0 ap1 (Array.repeat 16#usize NHI_Scalar.zero)
 let value←FIo_Native.weights.grouped_inactive_pair w f low
 let parts0←Array.update parts 0#usize value
 let b←FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant .S2
 let libra←if b then FIo_Native.weights.factored_s2_libra_weights ap0 ap1 w.extra
  else FIo_Native.weights.twofold_libra_weights low w.extra
 let parts4←NIG_LibraLoop.reference f libra parts0
 let powers←FIo_Native.weights.powers 7#usize kappa
 let sum←NHX_FinalLoop.reference parts4 powers
 ok (.Ok sum)

theorem source (w:W) (f:Slice U8) (ap0 ap1:Powers) (kappa:NE) (parts:Parts)
 (s2:w.variant=FIo_Native.transport.Variant.S2):
 dispatch w f ap0 ap1 kappa parts=NIG_TailControl.reference w f ap0 ap1 kappa parts:=by
 unfold dispatch NIG_TailControl.reference
 simp only [s2,FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq,bind_tc_ok]
 rfl
#print axioms source
end NIG_PairSuffix
