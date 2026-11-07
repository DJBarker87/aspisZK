"""Strict resumed evidence validation. Historical receipts are preserved."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess,collections
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l)for l in (E/'NMT_ATTEMPTS.jsonl').read_text().splitlines()]
launched=[r for r in rows if 'exit_status'in r]
new=[r for r in launched if r['attempt'].startswith('NMT_L')and int(r['attempt'][5:])>60]
assert len(new)<=250 and len({r['attempt']for r in launched})==len(launched)
assert {r['attempt']for r in launched if r['kind']=='extract'}=={'NMT_E001','NMT_E002','NMT_E003'}
assert not any(r['kind']=='kani'for r in launched)
assert [int(r['attempt'][5:])for r in new]==list(range(61,61+len(new)))
share=[json.loads(l)for l in (E/'NMT_SHARE.jsonl').read_text().splitlines()]
disk=[json.loads(l)for l in (E/'NMT_DISK.jsonl').read_text().splitlines()]
seen={}
for r in launched:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert any(s['attempt']==a and s['count']<6 for s in share)
 assert any(s['attempt']==a and s['free_bytes']>=40_000_000_000 for s in disk)
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert int(r['swaps'])==0
 if r['kind']=='lean':assert '-M7000'in r['command']
 if r['exit_status']==0:assert not any('sorryAx'in s for s in r.get('print_axioms',[]))
 assert r['source_revision'] and r['deps_fingerprint_ref']['sha256']==sha((E/a/'receipt.json').read_bytes())
 if r in new:
  for path,h in r['source_hashes'].items():
   if path.endswith('.lean'):
    k=(r['module'],h);assert k not in seen or seen[k]['exit_status']==0,(seen.get(k),r)
    seen[k]=r
idx=json.loads((E/'NMT_INPUTS.json').read_text())
for h,item in idx['objects'].items():
 p=E/item['path'];assert sha(p.read_bytes())==item['archive_sha256'];raw=lzma.decompress(p.read_bytes());assert sha(raw)==h and len(raw)==item['bytes']
for a,files in idx['attempts'].items():
 r=json.loads((E/a/'receipt.json').read_text())
 for n,h in files.items():assert r['source_hashes'][n]==h
pairs=0
for p in E.rglob('*.xz'):
 q=p.with_suffix('');s=q.with_name(q.name+'.sha256')
 if s.is_file():assert sha(lzma.decompress(p.read_bytes()))==s.read_text().strip();pairs+=1
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
current=json.loads((E/'NMT_RESUME_MODULES.json').read_text())
for m,h in current['passing_sources'].items():
 p=E/(m+'.lean');assert sha(p.read_bytes())==h
 assert not re.search(r'^\s*(?:axiom|sorry|admit)\b',p.read_text(),re.M)
 assert 'native_decide'not in p.read_text()
audit=json.loads((E/'NMT_RESUME_AUDIT.json').read_text())
assert audit['standard_only']and audit['collector_equal']and audit['own_roots']==len(current['new_roots'])
actual=[]
for g in audit['groups']:
 mode=g['mode'];raw=json.loads((E/'NMT_raw'/mode/'NMT_audit'/mode/(mode+'.json')).read_text())
 assert raw['exit_status']==0 and int(raw['swaps'])==0
 for result in raw['results']:
  assert result['equal']and set(result['walked_axioms'])<=set(['propext','Classical.choice','Quot.sound'])
  actual.append(result['root'])
assert len(actual)==len(set(actual))and set(actual)==set(current['new_roots'])
assert any(r.get('module')=='NMT_RESUME_COMBINED_IMPORT'and r['exit_status']==0 and sha((E/'NMT_RESUME_COMBINED_IMPORT.lean').read_bytes())in r['source_hashes'].values()for r in new)
assert json.loads((E/'NMT_CLOSED.json').read_text())['credit_requested']==0
for line in subprocess.check_output(['git','status','--porcelain','--untracked-files=all'],text=True).splitlines():assert line[3:].startswith('evidence/tx1-owned-20261111/'),line
summary=dict(status='PASS_EVIDENCE_ONLY_CANONICAL_ROWS_OPEN',resumed_scopes=len(new),scope_budget=250,scope_remaining=250-len(new),new_extractions=0,new_kani=0,resumed_failures=sum(r['exit_status']!=0 for r in new),new_modules=len(current['new_modules']),new_raw_roots=audit['own_roots'],standard_axioms=['propext','Classical.choice','Quot.sound'],resumed_wall_seconds=sum(r['wall_seconds']for r in new),resumed_peak_rss_kib=max(int(r['peak_rss_kib'])for r in new),swaps=0,compressed_sha_pairs=pairs,input_objects=len(idx['objects']),candidate_rows=0,spec_findings=['NMT-S1','NMT-S2'],source_commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'NMT_RESUME_VALIDATION.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
