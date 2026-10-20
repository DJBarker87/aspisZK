from pathlib import Path
import json,hashlib,re,subprocess
p=Path(__file__).resolve().parent;r=next(q for q in p.parents if (q/'.git').exists());sha=lambda b:hashlib.sha256(b).hexdigest()
e=p/'extraction';pins=json.loads((e/'input/source-pins.json').read_text())
for c in pins['cuts']:
 b=subprocess.check_output(['git','show',pins['revision']+':'+c['path']],cwd=r)[c['start_byte']:c['end_byte_exclusive']]
 assert sha(b)==c['sha256']
 assert b==(e/'input/fragments/backward.rs').read_bytes()
 assert b.decode() in (e/'input/lib.rs').read_text()
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
g=e/'generated/AspisR1BatchBackward'
assert clean((g/'Types.lean').read_text())==(p/'sources/AspisR1BatchBackward/Types.lean').read_text()
s=clean((g/'Funs.lean').read_text()).replace('import AspisR1BatchBackward.FunsExternal\n','')
for n in ['backward_loop.body','backward_loop','backward']:
 s=s.replace('def '+n+'\n','def '+n+'\n  (mul : field.M31 → field.M31 → Result field.M31)\n'+('  (inv : field.M31 → Result field.M31)\n' if n=='backward' else ''))
s=s.replace('field.M31.mul','mul').replace('field.M31.inv product','inv product').replace('backward_loop.body flat','backward_loop.body mul flat').replace('backward_loop iter','backward_loop mul iter')
assert s==(p/'sources/BatchBackwardExplicitOps.lean').read_text()
old=(p/'dependencies/reused/ExtractedMaskReverseRange.lean').read_text()
new=(p/'sources/BatchBackwardRangeFacts.lean').read_text()
old=old.replace('import AspisR1SelectedMaskProbe.Funs','import BatchBackwardExplicitOps\nimport Aeneas.Std.RangeIter').replace('namespace AspisR1.ExtractedMaskReverseRange','namespace AspisR1BatchBackward.Proof').replace('end AspisR1.ExtractedMaskReverseRange','end AspisR1BatchBackward.Proof')
assert old==new
old=(p/'dependencies/reused/BatchedWeightsVecResizeLengthGenericV1.lean').read_text()
lemma=old[old.index('theorem resize_success_length'):old.index('#print axioms')]
assert lemma in (p/'sources/BatchBackwardEntrypoint.lean').read_text()
m=json.loads((p/'manifest.json').read_text())
for x in m['modules']:
 assert sha((p/x['source']).read_bytes())==x['source_sha256']
 rc=json.loads((p/x['receipt']).read_text());assert rc['exit_status']==0 and rc['scope_swap_peak_bytes']==0
 assert 'sorryAx' not in (p/Path(x['receipt']).parent/'lean.log').read_text()
print('PASS: exact frozen backward span, mul/inv-only emitted interface, unchanged reused range/resize proofs, selected green pins')
