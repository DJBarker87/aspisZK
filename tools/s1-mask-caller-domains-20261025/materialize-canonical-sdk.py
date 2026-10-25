#!/usr/bin/env python3
"""Strengthen the SAME installed SDK theorem with its actual canonical mask."""
from pathlib import Path
import json,hashlib,sys
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';base=S/'S1SdkReachedMaskInputsV1.lean';old=base.read_text();s=old
s=s.replace('import S1SdkMaskInputRangesV1\nimport S1ReachedMaskInputsV1','import S1SdkReachedMaskInputsV1\nimport S1ReachedMaskCanonicalV1').replace('AspisS1SdkReachedMaskInputs','AspisS1SdkCanonicalMask').replace('original_sdk_reached_mask_input_ranges','original_sdk_canonical_mask')
a=s.index('/-- SAME original');b=s.index('theorem original_sdk_canonical_mask',a)
s=s[:a]+'''/-- SAME original SDK acceptance, existing complete semantic/preparation
witness and exact installed selector/mask source instance. The reached mask
output's four-word canonicality is derived, not a source/caller hypothesis.
All prior SDK/Std/extraction/SourceCuts/native/other-finish boundaries remain. -/
'''+s[b:]
needle='''        AspisS1ReachedMaskInputs.ReachedMaskInputRanges
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install base))) (retainedSem sem) ∧
''';assert s.count(needle)==1
s=s.replace(needle,needle+'''        AspisS1ReachedMaskCanonical.ReachedCanonicalMask
          (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children (AspisS1SourceMaskOps.install base))) (retainedSem sem) ∧
''')
s=s.replace('AspisS1SdkMaskInputRanges.original_sdk_selected_mask_input_ranges','AspisS1SdkReachedMaskInputs.original_sdk_reached_mask_input_ranges')
needle='''      L sdk copy std allocator e world admission adapterOps ops (AspisS1SourceMaskOps.install base) native1 native2 hashv extraction
''';assert s.count(needle)==1;s=s.replace(needle,'''      L sdk copy std allocator e world admission adapterOps ops base native1 native2 hashv extraction
''')
s=s.replace('numeric,challengeRanges,cells,maskDomains,\n    seeds,','numeric,challengeRanges,cells,maskDomains,reached,\n    seeds,')
a=s.index('  have verify :');b=s.index('  exact ⟨selectedPublic',a)
s=s[:a]+'''  have canonical := AspisS1ReachedMaskCanonical.canonical_of_reached_inputs _ _ reached
'''+s[b:]
a=s.index('  exact ⟨selectedPublic');s=s[:a]+s[a:].replace('numeric,challengeRanges,cells,maskDomains,reached,\n    seeds,','numeric,challengeRanges,cells,maskDomains,reached,canonical,\n    seeds,')
def signature(x):return x[x.index(' {W A M Cv : Type}'):x.index(' :\n    post =')]
assert signature(old)==signature(s)
out=S/'S1SdkCanonicalMaskV1.lean'
if '--check' in sys.argv:assert out.read_text()==s;print('PASS exact SDK binders and prior source instance; only actual canonical-mask postcondition added')
else:
 assert not out.exists()or '--refresh'in sys.argv;out.write_text(s)
 (Path(__file__).parent/'canonical-binding.json').write_text(json.dumps(dict(base=str(base.relative_to(R)),base_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),target=str(out.relative_to(R)),target_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),prior_binders_byte_identical=True,added_caller_hypotheses=False,whole_sdk_native_refinement=False,added_postcondition='ReachedCanonicalMask on same D and retainedSem sem'),indent=2)+'\n')
