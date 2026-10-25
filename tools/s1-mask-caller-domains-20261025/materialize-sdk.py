#!/usr/bin/env python3
"""Strengthen the same SDK theorem; exact old binders/post retained plus domain."""
from pathlib import Path
import hashlib,json,sys
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';base=S/'S1SdkClaimInputRangesV1.lean';old=base.read_text();s=old
s=s.replace('import S1SdkSelectedSemanticTraceV1\nimport S1ClaimAcceptedCallerRangesV1','import S1SdkClaimInputRangesV1\nimport S1MaskCallerDomainsV1')
s=s.replace('namespace AspisS1SdkClaimInputRanges','namespace AspisS1SdkMaskInputRanges').replace('end AspisS1SdkClaimInputRanges','end AspisS1SdkMaskInputRanges').replace('original_sdk_selected_claim_input_ranges','original_sdk_selected_mask_input_ranges')
start=s.index('/-- SAME original SDK');end=s.index('theorem original_sdk_selected_mask_input_ranges',start)
s=s[:start]+'''/-- SAME original SDK acceptance and complete semantic witness also supply
both concrete mask selector executions and all their input ranges. No new
caller, Claims-producer, successful selector or canonicality premise is added.
SDK/Std/runtime/allocator/extraction/SourceCuts remain the prior boundaries. -/
'''+s[end:]
needle='        AspisS1ClaimAcceptedCallerRanges.CurrentClaimsNumeric sem ∧\n';assert s.count(needle)==1;s=s.replace(needle,needle+'        AspisS1MaskCallerDomains.MaskInputRanges (retainedSem sem) ∧\n')
s=s.replace('AspisS1SdkSelectedSemanticTrace.original_sdk_selected_semantic_trace','AspisS1SdkClaimInputRanges.original_sdk_selected_claim_input_ranges')
s=s.replace('viewCall,variant,semanticCall,preparedCall,powers,early,claimed,numeric,challengeRanges,\n    seeds,','viewCall,variant,semanticCall,preparedCall,powers,early,claimed,numeric,challengeRanges,cells,\n    seeds,')
start=s.index('  have cells :');end=s.index('  exact ⟨selectedPublic',start)
s=s[:start]+'''  have maskDomains : AspisS1MaskCallerDomains.MaskInputRanges (retainedSem sem) :=
    AspisS1MaskCallerDomains.accepted_claim_mask_inputs
      (retainedDigest (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues AspisS1ExtractedRoundChildren.children B))
      (retainedSem sem) view.y1 (AspisR1SelectedWideViewV1.prepCarrier view.inactive)
      prepared.kappa prepared.claim scratch claimed numeric
'''+s[end:]
i=s.index('  exact ⟨selectedPublic');s=s[:i]+s[i:].replace('numeric,challengeRanges,cells,\n    seeds,claimMeaning','numeric,challengeRanges,cells,maskDomains,\n    seeds,claimMeaning')
# Quantified statement and every pre-existing conjunct must stay byte-identical.
def signature(x):return x[x.index(' {W A M Cv : Type}'):x.index(' :\n    post =')]
assert signature(old)==signature(s)
out=S/'S1SdkMaskInputRangesV1.lean'
if '--check' in sys.argv:assert out.read_text()==s;print('PASS deterministic SDK source, exact prior binders and one extra conjunct')
else:
 assert not out.exists() or '--refresh' in sys.argv;out.write_text(s)
 (Path(__file__).parent/'binding.json').write_text(json.dumps(dict(base=str(base.relative_to(R)),base_sha256=hashlib.sha256(base.read_bytes()).hexdigest(),target=str(out.relative_to(R)),target_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),prior_binders_byte_identical=True,added_caller_hypotheses=False,added_conjunct='AspisS1MaskCallerDomains.MaskInputRanges (retainedSem sem)',whole_source_closed=False),indent=2)+'\n')
