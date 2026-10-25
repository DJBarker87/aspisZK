#!/usr/bin/env python3
"""Fix exact selector/mask operations and retain the SAME accepted SDK run."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';base=S/'S1SdkMaskInputRangesV1.lean';s=base.read_text()
s=s.replace('import S1SdkClaimInputRangesV1\nimport S1MaskCallerDomainsV1','import S1SdkMaskInputRangesV1\nimport S1ReachedMaskInputsV1').replace('AspisS1SdkMaskInputRanges','AspisS1SdkReachedMaskInputs').replace('original_sdk_selected_mask_input_ranges','original_sdk_reached_mask_input_ranges')
a=s.index('/-- SAME original SDK');b=s.index('theorem original_sdk_reached_mask_input_ranges',a)
s=s[:a]+'''/-- SAME original accepted SDK run with exact selector/mask operations fixed.
The semantic verifier and its later claim supply the reached mask call and
input ranges. The other full finish, SDK/Std/native/source boundaries remain.
This specializes prior B; it adds no SDK or canonicality hypothesis. -/
'''+s[b:]
s=s.replace('    (B : AspisR1PublicPreparation.FinishModel.Boundaries)','    (base : AspisR1PublicPreparation.FinishModel.Boundaries)')
needle='        AspisS1MaskCallerDomains.MaskInputRanges (retainedSem sem) ∧\n';assert s.count(needle)==1
s=s.replace(needle,needle+'''        AspisS1ReachedMaskInputs.ReachedMaskInputRanges
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)) (retainedSem sem) ∧
''')
s=s.replace('AspisS1SdkClaimInputRanges.original_sdk_selected_claim_input_ranges','AspisS1SdkMaskInputRanges.original_sdk_selected_mask_input_ranges')
s=s.replace('numeric,challengeRanges,cells,\n    seeds,','numeric,challengeRanges,cells,maskDomains,\n    seeds,')
a=s.index('  have maskDomains :');b=s.index('  exact ⟨selectedPublic',a)
s=s[:a]+'''  have verify : S1SemanticInstallation.verify AspisS1ExtractedRoundChildren.children B
      (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
      _ view.semantic () = ok (.Ok sem) := semanticCall
  have reached := AspisS1ReachedMaskInputs.source_verify_reached_mask_inputs base
    (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B)
    _ view.semantic () sem verify view.y1 (AspisR1SelectedWideViewV1.prepCarrier view.inactive)
    prepared.kappa prepared.claim scratch claimed
'''+s[b:]
a=s.index('  exact ⟨selectedPublic');s=s[:a]+s[a:].replace('numeric,challengeRanges,cells,maskDomains,\n    seeds,','numeric,challengeRanges,cells,maskDomains,reached,\n    seeds,')
s=re.sub(r'\bB\b','(AspisS1SourceMaskOps.install base)',s)
out=S/'S1SdkReachedMaskInputsV1.lean'
if '--check' in sys.argv:assert out.read_text()==s;print('PASS two concrete source operations; same SDK boundaries, one reached-call conjunct')
else:
 assert not out.exists() or '--refresh'in sys.argv;out.write_text(s)
 (Path(__file__).parent/'reached-binding.json').write_text(json.dumps(dict(base=str(base.relative_to(R)),base_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),target=str(out.relative_to(R)),target_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),specialization='B = AspisS1SourceMaskOps.install base (only fromFn/mask fixed)',added_sdk_or_numeric_hypotheses=False,other_finish_fields_still_parameters=True,original_sdk_native_refinement_proved=False),indent=2)+'\n')
