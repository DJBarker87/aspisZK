import NDO_JGv_PairShared0
import NDO_JGq_SharedHigh
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGv_PairShared1
open Aeneas Aeneas.Std Result ControlFlow
open JGq_PairShape
abbrev E := FIo_Install.NE
def low (parts : Array E 7#usize) : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
  let low := Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
  let low1 ← FIo_Native.weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize} JGq_Powers0.a4 JGq_Powers1.a4 low
  let inactive ← FIo_Native.weights.grouped_inactive_pair w f low1
  let written ← Array.update parts 0#usize inactive
  let b ← FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant .S2
  let libra ← if b then FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4 w.extra
    else FIo_Native.weights.twofold_libra_weights low1 w.extra
  let out ← FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f written libra
  let powers ← FIo_Native.weights.powers 7#usize kappa
  let sum ← FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} out powers FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
  ok (.Ok sum)
theorem source (parts : Array E 7#usize) : JGv_PairShared0.shared parts=low (JGq_SharedHigh.write parts) := by
  have common : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w
      (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (w,JGq_Common.a16) := by
    with_unfolding_all exact JGq_Common.source
  have partials : FIo_Native.weights.shared_partials f JGq_Common.a16=ok (.Ok JGq_SharedPartials.value) := by
    with_unfolding_all exact JGq_SharedPartials.source
  have high : FIo_Native.weights.shared_high JGq_SharedPartials.value w JGq_Powers0.a4 JGq_Powers1.a4 parts=
      ok (.Ok (),JGq_SharedHigh.write parts) := by
    with_unfolding_all exact JGq_SharedHigh.source parts
  unfold JGv_PairShared0.shared low
  simp only [common,partials,high,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
    show ¬(2#usize=1#usize) from by decide,ite_false]
#print axioms source
end AspisR1.JGv_PairShared1
end
