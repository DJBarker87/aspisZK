import JGq_PairCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGq_PairAfterShared
open Aeneas Aeneas.Std Result ControlFlow
open JGq_PairShape
abbrev E := FIo_Install.NE

/-- The actual remaining Pair calls; no successful regular, inactive, Libra,
final sum or comparison has been supplied as an input proposition. -/
def remaining : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
  let (r,_,parts) ← FIo_Native.weights.process_regular_kinds w true alpha f 2#usize 64#usize
    JGq_Powers0.a4 JGq_Powers1.a4 scratch JGq_PairPrefix.initial
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue _ => do
    let inactive ← FIo_Native.weights.grouped_inactive_pair w f JGq_Low.a16
    let lowParts ← Array.update (JGq_SharedHigh.write parts) 0#usize inactive
    let libra ← FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4 w.extra
    let lastParts ← FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f lowParts libra
    let sum ← FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} lastParts JGq_PowersK.a7
      FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
    ok (.Ok sum)
  | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      E (core.convert.FromSame FIo_Native.verifier.Error) residual

/-- Eliminates only computed source calls under the actual earlier regular
return, retaining all branches and the source order. -/
theorem source : JGq_PairPrefix.remaining=remaining := by
  have common : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w
      (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (w,JGq_Common.a16) := by
    with_unfolding_all exact JGq_Common.source
  have partials : FIo_Native.weights.shared_partials f JGq_Common.a16=ok (.Ok JGq_SharedPartials.value) := by
    with_unfolding_all exact JGq_SharedPartials.source
  have high : ∀ before,FIo_Native.weights.shared_high JGq_SharedPartials.value w JGq_Powers0.a4 JGq_Powers1.a4 before=
      ok (.Ok (),JGq_SharedHigh.write before) := by
    intro before
    with_unfolding_all exact JGq_SharedHigh.source before
  have powerk : FIo_Native.weights.powers 7#usize kappa=ok JGq_PowersK.a7 := by
    with_unfolding_all exact JGq_PowersK.source
  unfold JGq_PairPrefix.remaining remaining
  simp only [ite_true,show ¬(2#usize=1#usize) from by decide,ite_false,
    common,partials,high,JGq_Low.source,powerk,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,Aeneas.Std.uncurry]
#print axioms source
end AspisR1.JGq_PairAfterShared
end
