#!/usr/bin/env python3
"""Attach final source arithmetic to the SAME prior conditional SDK witness."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';base=S/'S1SdkCanonicalMaskV1.lean';old=base.read_text();s=old
s=s.replace('import S1SdkReachedMaskInputsV1\nimport S1ReachedMaskCanonicalV1','import S1SdkCanonicalMaskV1\nimport S1ReachedFinalNumericV1').replace('namespace AspisS1SdkCanonicalMask','namespace AspisS1SdkFinalArithmetic').replace('end AspisS1SdkCanonicalMask','end AspisS1SdkFinalArithmetic').replace('theorem original_sdk_canonical_mask','theorem original_sdk_final_arithmetic').replace('#print axioms original_sdk_canonical_mask','#print axioms original_sdk_final_arithmetic')
a=s.index('/-- SAME original');b=s.index('theorem original_sdk_final_arithmetic',a)
s=s[:a]+'''/-- SAME conditional original SDK/source witness with actual mask/selector
and final add/mul operations fixed. The reached product/sum/extra/target
ranges have no numeric input premise, including no Terminal range premise.
Native/extraction/SourceCuts and other finish interfaces remain explicit. -/
'''+s[b:]
s=s.replace('    (base : AspisR1PublicPreparation.FinishModel.Boundaries)','    (backend : AspisR1PublicPreparation.FinishModel.Boundaries)')
s=re.sub(r'\bbase\b','(AspisS1SourceFinalOps.install backend)',s)
D='(retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))))'
public='''(FirstComposition.toRetainedPublic (FirstComposition.toCurrentPublic
            (AspisR1PublicPreparation.PreparationBinding.preparationPublic
              (AspisS6CurrentAdapterCarrier.toPoolV1PairForestTerminalStatementV1 f.statement))))'''
needle='''        AspisS1ReachedMaskCanonical.ReachedCanonicalMask
          '''+D+''' (retainedSem sem) ∧
''';assert s.count(needle)==1
extra='''        AspisS1ReachedFinalNumeric.ReachedFinalNumeric backend
          '''+D+''' '''+public+''' (retainedSem sem) ∧
'''
s=s.replace(needle,needle+extra)
s=s.replace('AspisS1SdkReachedMaskInputs.original_sdk_reached_mask_input_ranges','AspisS1SdkCanonicalMask.original_sdk_canonical_mask')
a=s.index('  obtain ⟨selectedPublic');b=s.index(' := allCuts accounts2 f s cuts',a)
s=s[:a]+s[a:b].replace('maskDomains,reached,\n    seeds,','maskDomains,reached,canonical,\n    seeds,')+s[b:]
a=s.index('  have canonical :=');b=s.index('  exact ⟨selectedPublic',a)
s=s[:a]+'''  have verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children
      (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend))
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))
      _ view.semantic () = ok (.Ok sem) := semanticCall
  have finalNumeric := AspisS1ReachedFinalNumeric.verify_final_numeric backend
    (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install (AspisS1SourceFinalOps.install backend)))
    _ view.semantic () sem verify view.y1 (AspisR1SelectedWideViewV1.prepCarrier view.inactive)
    prepared.kappa prepared.claim scratch claimed
'''+s[b:]
a=s.index('  exact ⟨selectedPublic');s=s[:a]+s[a:].replace('maskDomains,reached,canonical,\n    seeds,','maskDomains,reached,canonical,finalNumeric,\n    seeds,')
out=S/'S1SdkFinalArithmeticV1.lean'
if '--check' in sys.argv:assert out.read_text()==s;print('PASS deterministic four-operation SDK instance; old conclusions plus reached final arithmetic, no new numeric hypothesis')
else:
 assert not out.exists()or '--refresh'in sys.argv;out.write_text(s)
 (Path(__file__).parent/'sdk-binding.json').write_text(json.dumps(dict(base=str(base.relative_to(R)),base_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),target=str(out.relative_to(R)),target_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),specialization='prior base := AspisS1SourceFinalOps.install backend (add/mul only); prior selector/mask installation retained',added_caller_numeric_or_child_success_hypotheses=False,range_result_requires_terminal_canonicality=False,exact_multiplication_formula_still_conditional=True,whole_native_sdk_refinement=False,added_conjunct=extra),indent=2)+'\n')
