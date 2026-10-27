from pathlib import Path
import sys,textwrap
R=Path(__file__).resolve().parents[2];out={}
def head(imports,ns):return '\n'.join('import '+v for v in imports)+f'\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{ns}\nopen Aeneas Aeneas.Std Result ControlFlow\nopen JGq_PairShape\nabbrev E := FIo_Install.NE\n'
def end(ns):return f'end AspisR1.{ns}\nend\n'
source=(R/'lean/JGq_PairPrefix.lean').read_text();a=source.index('      let common :=');b=source.index('\n    else\n      if 2#usize',a);body=textwrap.dedent(source[a:b]);body=body.replace('parts1','parts')
ns='JGs_PairShared0';s=head(['JGs_Regular'],ns)+'''def shared (parts : Array E 7#usize) : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
'''+textwrap.indent(body,'  ')+'\n'
s+='''theorem source : JGq_PairPrefix.remaining=shared JGs_K4.parts := by
  unfold JGq_PairPrefix.remaining shared
  rw [JGs_Regular.source,bind_tc_ok]
  simp only [Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,ite_true]
#print axioms source
'''+end(ns);out[ns]=s
# Actual low continuation after the shared write; branch folds=2 has already been chosen.
a=body.index('    let low :=');b=body.index('\n| core.ops.control_flow.ControlFlow.Break residual',a) if '\n| core.ops.control_flow.ControlFlow.Break residual' in body[a:] else len(body)
# Use explicit small source tail rather than the duplicated discarded one-fold branch.
tail='''  let low := Array.repeat 16#usize FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO
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
'''
ns='JGs_PairShared1';s=head(['JGs_PairShared0','JGq_SharedHigh'],ns)+'''def low (parts : Array E 7#usize) : Result (core.result.Result E FIo_Native.verifier.Error) :=
  letI := FIo_Install.allocation (.Ok ()); do
'''+tail+'''theorem source (parts : Array E 7#usize) : JGs_PairShared0.shared parts=low (JGq_SharedHigh.write parts) := by
  have common : FIo_Native.weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} w
      (Array.repeat 16#usize FIo_Native.aspis_core.field.QM31.ZERO)=ok (w,JGq_Common.a16) := by
    with_unfolding_all exact JGq_Common.source
  have partials : FIo_Native.weights.shared_partials f JGq_Common.a16=ok (.Ok JGq_SharedPartials.value) := by
    with_unfolding_all exact JGq_SharedPartials.source
  have high : FIo_Native.weights.shared_high JGq_SharedPartials.value w JGq_Powers0.a4 JGq_Powers1.a4 parts=
      ok (.Ok (),JGq_SharedHigh.write parts) := by
    with_unfolding_all exact JGq_SharedHigh.source parts
  unfold JGs_PairShared0.shared low
  simp only [common,partials,high,bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,
    show ¬(2#usize=1#usize) from by decide,ite_false]
#print axioms source
'''+end(ns);out[ns]=s
out['JGs_PairShared2']='import JGs_PairShared1\nimport JGq_Low\nimport JGs_Inactive\nimport JGs_LibraSource\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JGs_PairShared2\nopen Aeneas Aeneas.Std Result ControlFlow\nopen JGq_PairShape\nabbrev E := FIo_Install.NE\ndef write (parts : Array E 7#usize) : Array E 7#usize := parts.set 0#usize JGs_Inactive.pair12\ndef remaining (parts : Array E 7#usize) : Result (core.result.Result E FIo_Native.verifier.Error) :=\n  letI := FIo_Install.allocation (.Ok ()); do\n  let out ← FIo_Native.weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f (write parts) JGs_LibraEnd.value\n  let sum ← FIo_Native.weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} out JGq_PowersK.a7 FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO\n  ok (.Ok sum)\ntheorem source (parts : Array E 7#usize) : JGs_PairShared1.low parts=remaining parts := by\n  have variant : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq w.variant .S2=ok true := by\n    change FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq .S2 .S2=ok true\n    unfold FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq FIo_Native.transport.Variant.read_discriminant\n    simp only [eq_self,decide_true]\n  have powers : FIo_Native.weights.powers 7#usize kappa=ok JGq_PowersK.a7 := by\n    with_unfolding_all exact JGq_PowersK.source\n  have inactive : FIo_Native.weights.grouped_inactive_pair w f JGq_Low.a16=ok JGs_Inactive.pair12 := JGs_Inactive.source\n  have libra : FIo_Native.weights.factored_s2_libra_weights JGq_Powers0.a4 JGq_Powers1.a4 w.extra=ok JGs_LibraEnd.value := by\n    with_unfolding_all exact JGs_LibraSource.source\n  have update : Array.update parts 0#usize JGs_Inactive.pair12=ok (write parts) := by\n    obtain ⟨after,call,value⟩ := WP.spec_imp_exists (Array.update_spec parts 0#usize JGs_Inactive.pair12 (by scalar_tac))\n    subst after\n    exact call\n  unfold JGs_PairShared1.low remaining\n  simp only [JGq_Low.source,variant,powers,inactive,libra,update,bind_tc_ok,ite_true]\n#print axioms source\n/-- Exact forward Pair prefix; only the final Libra contraction and seven-part sum remain. -/\ntheorem native_remaining : @FIo_Native.weights.Weights.pair (FIo_Install.allocation (.Ok ()))\n    w alpha f kappa=remaining (JGq_SharedHigh.write JGs_K4.parts) := by\n  rw [JGq_PairPrefix.native,JGs_PairShared0.source,JGs_PairShared1.source,source]\n#print axioms native_remaining\nend AspisR1.JGs_PairShared2\nend\n'
for mod,s in out.items():
 p=R/'lean'/(mod+'.lean')
 if '--check' in sys.argv:assert (p if p.exists() else R/'evidence/fixture-tx2p-20261027/JGs_UNCHECKED'/(p.name+'.txt')).read_text()==s,mod
 else:p.write_text(s)
print(len(out),'split parent continuations')
