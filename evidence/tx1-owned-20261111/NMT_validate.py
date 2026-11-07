"""Local evidence validation; no compiler, solver, build or host mutation."""
from pathlib import Path
import json,lzma,hashlib,re,collections,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()];launched=[r for r in rows if 'exit_status'in r]
assert len(launched)==63
assert {r['attempt']for r in launched if r['kind']=='extract'}=={f'NMT_E{i:03}'for i in range(1,4)}
assert {r['attempt']for r in launched if r['kind']!='extract'}=={f'NMT_L{i:03}'for i in range(1,61)}
share=[json.loads(l)for l in (E/'NMT_SHARE.jsonl').read_text().splitlines()]
for r in launched:
 ad=json.loads((E/(r['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert any(s['attempt']==r['attempt']and s['count']<6 for s in share)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 if r['kind']=='lean':assert '-M7000'in r['command']
 if r['exit_status']==0:assert not any('sorryAx'in s for s in r['print_axioms'])
 assert r['source_revision'] and r['deps_fingerprint_ref']['sha256']==sha((E/r['attempt']/'receipt.json').read_bytes())
idx=json.loads((E/'NMT_INPUTS.json').read_text())
for h,item in idx['objects'].items():
 p=E/item['path'];assert sha(p.read_bytes())==item['archive_sha256'];raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and len(raw)==item['bytes']
for a,files in idx['attempts'].items():
 r=json.loads((E/a/'receipt.json').read_text())
 for n,h in files.items():assert r['source_hashes'][n]==h
pairs=0
for p in E.rglob('*.xz'):
 raw=lzma.decompress(p.read_bytes());q=p.with_suffix('');s=q.with_name(q.name+'.sha256')
 # Content-addressed input archives have hashes in NMT_INPUTS instead.
 if s.is_file():assert s.read_text().strip()==sha(raw);pairs+=1
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
current=json.loads((E/'NMT_CURRENT_MODULES.json').read_text())
for m,h in current['passing_sources'].items():
 p=E/(m+'.lean');assert sha(p.read_bytes())==h
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b',p.read_text(),re.M)
 assert 'native_decide'not in p.read_text()
audit=json.loads((E/'NMT_AUDIT.json').read_text());assert audit['standard_only']and audit['collector_equal']and audit['own_roots']==58
paths=subprocess.check_output(['git','diff','--name-only','HEAD'],text=True).splitlines();assert all(p.startswith('evidence/tx1-owned-20261111/')for p in paths)
summary=dict(status='PASS_WITH_RECORDED_PROCESS_ERROR_AND_OPEN_ROWS',attempts=63,extractions=3,lean_link_audit=60,kani=0,failed_elaborations=sum(r['exit_status']!=0 for r in launched),own_modules=len(current['modules']),own_raw_roots=58,compressed_sha_pairs=pairs,input_objects=len(idx['objects']),wall_seconds=sum(r['wall_seconds']for r in launched),peak_rss_kib=max(int(r['peak_rss_kib'])for r in launched),swaps=0,duplicate_failed_source='L005/L006 explicitly retained; no credit',candidate_rows=0)
(E/'NMT_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
