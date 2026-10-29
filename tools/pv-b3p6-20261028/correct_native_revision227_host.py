"""Preserve and correct a receipt-only revision-label transcription mistake.
Never reruns a native gate. Exact frozen source content is independently checked.
"""
from pathlib import Path
import json,hashlib,sys
from run import H
label=sys.argv[1];assert label in ('native227-resume5-owned-parts','fidelity227-resume5-native')
revision=(H/'revision').read_text().strip();freeze=json.loads((H/'native227-parts-source-freeze.json').read_text());assert all(hashlib.sha256((H/'source'/n).read_bytes()).hexdigest()==sha for n,sha in freeze.items())
p=H/label/'receipt/receipt.json';raw=p.read_bytes();r=json.loads(raw);assert r['exit_status']==0
if r['source_revision']!=revision:
 old=p.parent/'receipt-original-revision-label.json';assert not old.exists();old.write_bytes(raw)
 correction=dict(original_recorded_revision=r['source_revision'],correct_revision=revision,original_receipt_sha256=hashlib.sha256(raw).hexdigest(),reason='manual CLI metadata-label typo; Rust inputs independently pinned by720 checked source hashes; no gate rerun',source_freeze='native227-parts-source-freeze.json')
 r['source_revision_correction']=correction;r['source_revision']=revision;p.write_text(json.dumps(r,indent=2)+'\n')
 feature='native227-parts-features' if label.startswith('native')else'fidelity227-resume5-features';q=H/(feature+'.json');before=q.read_bytes();(H/(feature+'-original-revision-label.json')).write_bytes(before);x=json.loads(before);x['revision'if feature.startswith('native')else'source_revision']=revision;x['source_revision_correction']=correction;q.write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps({k:r[k]for k in ('exit_status','wall_seconds','peak_rss_kib','swaps','source_revision')}))
