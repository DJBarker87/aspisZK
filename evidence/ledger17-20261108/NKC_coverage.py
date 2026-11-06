from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;S=E.parent/'tx2-decoders3-20261108';Q=E.parent/'tx2-decoders2-20261108'
J=lambda p:json.loads(p.read_text());H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
closed=J(S/'NJY_CLOSED.json')['functions'];items=[]
branches={
 '149':['wrong width before payload reads','wrong magic','wrong version','reserved5..8 then108..112','asset104 >=2147483647 -> NonCanonicalAssetId','Ok record pool8/mint40/token72/asset104/domain112'],
 '152':['wrong width192','ordered header/reserved176..192/nonzero master8..40/domain40..72','digest80..112 full error -> NonCanonicalDigest','eight word112+8*k: arbitrary-step induction; write BEFORE capacity rejection; no rejecting suffix','Ok complete record bump7/master8/domain40/sequence72/root80/all lanes112'],
 '153':['wrong width384','ordered header/reserved50..64 and312..320/format8..40','Boolean49 exactly0/1 else error','identity64..208 full Result mapped Identity','policy208..312 full Result mapped Policy','eight word320+8*k writes and full frame by induction','constructor bump7/identity/policy/mask48/has49/next40/lanes320','validator157 full Err unchanged or Ok same complete master'],
 '201':['wrong width192','magic/version/reserved184..192 prefix and no child log on rejection','status5 exact0..3 or InvalidStatus','complete record status5/version6/bump7/keys8,40,72,104,152/slots136,144','validator206 same-record full Err or Ok same complete record'],
 '203':['wrong width128','magic/version/reserved7 and120..128 prefix and no child log on rejection','complete record flags5/bump6/keys8,40,72/generation104/delay112','validator208 same-record full Err or Ok same complete record']}
for f in closed:
 n=f['rows'][0].split(':')[1];pair=f.get('native_pairs',[])+f.get('inherited_native_pairs',[])
 items.append(dict(row=f['rows'][0],reviewed_transcription=f['reviewed_transcription'],all_Result_error_and_record_arms=branches[n],native_segments=pair,lean_frame_composition=['NJQ_Identity.source']if n=='149'else[f'NJQ_{x}{s}'for x in [{'152':'Checkpoint','153':'Master','201':'Entry','203':'Registry'}[n]]for s in ['Cut.complete_record','Cut.cut_result','Total.native_source']],returned_record_fidelity=f['returned_record_fidelity'],record_fidelity_semantic_verdicts='positive SUCCESSFUL; inverted/unimplied/modifies controls FAILED, same names/configuration',review='Reviewed each complete definition and constructor; no success-only arm, free child reply, uninstantiated operation dictionary or hidden record coordinate.'))
inputs=[]
for p in [S/'NJY_CERTIFICATES.md',S/'NJY_HYPOTHESES.json',S/'NJY_REVIEWED_TRANSCRIPTIONS.json',S/'NJY_Roots.lean']+[Q/f'NJQ_{n}{s}.lean'for n in ['Checkpoint','Master','Entry','Registry']for s in ['Cut','Total']]+[Q/'NJQ_Identity.lean']:
 inputs.append(dict(path=str(p.relative_to(E.parents[1])),sha256=H(p)))
(E/'NKC_NJY_COVERAGE.json').write_text(json.dumps(dict(ruling='(ay)(3)/(4)',status='PASS_READ_ONLY_SEGMENT_FRAME_AND_RECORD_REVIEW',rows=items,input_pins=inputs,wrapper_consumers_48_49='OPEN; NJY-B1 retained',trust='ReviewedTranscription option-A reclassification only'),indent=1)+'\n')
print('NJY five-row Result/error/record coverage recorded')
