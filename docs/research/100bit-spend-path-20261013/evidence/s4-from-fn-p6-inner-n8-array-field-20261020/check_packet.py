from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((D/'manifest.json').read_text())
for f in m['files']:assert sha(D/f['path'])==f['sha256'],f['path']
assert m['schema']=='focused-extractor-proof-packet-v1'
for x in m['modules']:
 assert sha(D/x['source'])==x['source_sha256']
 rc=json.loads((D/x['receipt']).read_text());pf=json.loads((D/x['preflight']).read_text());prefix='receipts' 
 assert sha(D/x['receipt'])==x['receipt_sha256'] and rc['exit_status']==0
 assert rc['source_sha256']==pf['source_sha256']==x['source_sha256'] and rc['object_sha256']==x['object_sha256']
 assert rc['source_revision_at_launch']==x['source_revision'] and x['source_revision']!='eba5db3b72ac4bcbc499f35e1e4e66002370357d'
 assert x['swap_bytes']==0 and x['peak_rss_bytes']<8*2**30
 assert '-j1' in pf['argv'] and pf['argv'][pf['argv'].index('-M')+1]=='4400'
 for name,pin in pf['direct_imports'].items():assert m['direct_import_source_map'][name]['object_sha256']==pin['object_sha256']
 log=(D/(prefix+'/lean.log')).read_text();assert 'sorryAx' not in log and 'core.fmt.Formatter' not in log and 'error:' not in log
 for a in re.findall(r'depends on axioms:\s*\[([^]]*)\]',log):assert set(re.findall(r'[A-Za-z_][A-Za-z_0-9.]*',a))<={'propext','Classical.choice','Quot.sound'}
 assert re.findall(r'^import\s+([A-Za-z0-9_.]+)',(D/x['source']).read_text(),re.M)==x['direct_imports']
assert not any(f.suffix in ['.olean','.ilean','.ir','.o','.llbc','.so','.a','.exe'] for f in D.rglob('*') if f.is_file())
print('PASS: exact checked sources/imports, corrected launch provenance, caps, standard axioms; no replay or binaries')
