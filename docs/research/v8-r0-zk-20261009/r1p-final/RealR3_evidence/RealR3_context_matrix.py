"""Read-only final per-row caller matrix; no proof/build invocation."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
matrix=[]
libhash=None
for row in range(3,15):
 name='context-row03-v11' if row==3 else f'context-row{row:02}-v12'
 d=E/'receipts'/name;r=json.loads((d/'receipt.json').read_text());i=json.loads((E/(name+'-inputs.json')).read_text())
 assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in (d/'stdout.log').read_text(),name
 assert r['command'][-1]==f'RealR3_context_proofs::row{row:02}'
 for f,h in i['hashes'].items():assert hashlib.sha256((E/'snapshots'/name/(f+'.txt')).read_bytes()).hexdigest()==h
 if libhash is None:libhash=i['hashes']['lib.rs']
 assert libhash==i['hashes']['lib.rs'],name
 matrix.append({'row':row,'payload_bytes':32 if row==14 else 0,'prefix_bytes':79+5*(row-3),'name':name,'source_revision':i['source_revision'],'source_hashes':i['hashes'],'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'receipt_sha256':hashlib.sha256((d/'receipt.json').read_bytes()).hexdigest()})
(E/'RealR3_context-matrix.json').write_text(json.dumps({'rows':matrix,'callee_reuse':'RealR3_callee30-identity.json','scope':'scalar emission caller only, exact real prefix sizes; arbitrary prefix/state/counter/outcome; successful allocations; no oracle-law/real-message-provenance/RunJoin claim','new_trust_fields':[]},indent=2)+'\n')
print(json.dumps({'rows':len(matrix),'wall_seconds':sum(x['wall_seconds'] for x in matrix),'max_rss_kib':max(x['peak_rss_kib'] for x in matrix)},indent=2))
