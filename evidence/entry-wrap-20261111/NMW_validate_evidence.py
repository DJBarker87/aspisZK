"""Final local validation of receipts, own proof audits, sources and hygiene."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'NMW_INPUTS.json').read_text());checks=0
for h,x in idx['objects'].items():
 p=E/x['path'];assert sha(p.read_bytes())==x['archive_sha256'];raw=lzma.decompress(p.read_bytes());assert len(raw)==x['bytes'] and sha(raw)==h;checks+=1
entries=[json.loads(l) for l in (E/'NMW_ATTEMPTS.jsonl').read_text().splitlines()]
scopes=[x for x in entries if 'full_receipt' in x];assert len({x['attempt'] for x in scopes})==len(scopes)
for x in scopes:
 rc=json.loads((E/x['full_receipt']).read_text());assert sha((E/x['full_receipt']).read_bytes())==x['full_receipt_sha256']
 assert rc['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 assert float(rc['swaps'])==0
 ad=json.loads((E/(rc['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for p,h in rc['source_hashes'].items():assert idx['attempts'][rc['attempt']][p]==h
 if rc['kind']=='lean':assert '-M7000' in rc['command']
for p in E.glob('*-admission.json'):
 d=json.loads(p.read_text());assert d['exit']==0 and d['reservation']['allowed'] is True
for l in (E/'NMW_DISK.jsonl').read_text().splitlines():assert json.loads(l)['free_bytes']>=40_000_000_000
pairs=0
for p in E.rglob('*.sha256'):
 if p.name=='NMW_FROZEN_PAYLOAD.json.sha256':target=E/'NMW_FROZEN_PAYLOAD.json.xz'
 else:target=p.with_name(p.name.removesuffix('.sha256')+'.xz')
 if target.exists():assert sha(lzma.decompress(target.read_bytes()))==p.read_text().strip();pairs+=1
wanted=json.loads((E/'NMW_AUDIT_ROOTS.json').read_text())['roots'];audited={}
allowed={'propext','Classical.choice','Quot.sound'}
for p in (E/'NMW_audit').rglob('*.json'):
 d=json.loads(p.read_text());assert d['exit_status']==0
 for row in d['results']:
  assert row['equal'] is True and set(row['walked_axioms'])<=allowed and set(row['collect_axioms'])<=allowed
  assert row['root'] not in audited;audited[row['root']]=dict(row,receipt=str(p.relative_to(E)))
assert set(audited)==set(wanted)
modules=json.loads((E/'NMW_EXPORT_MODULES.json').read_text());latest={}
for rc in scopes:
 if rc['kind']=='lean' and rc['exit_status']==0:latest[rc['module']]=rc
for m in modules:
 p=E/(m+'.lean');assert p.exists();h=sha(p.read_bytes());assert h in latest[m]['source_hashes'].values(),m
 for line in re.findall(r'^theorem (\w+)',p.read_text(),re.M):assert '#print axioms '+line in p.read_text(),(m,line)
 code=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S)
 code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',code),m
# Generated raw/template evidence is retained uncompiled; only listed proof modules count.
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
counts={k:sum(x['kind']==k for x in scopes) for k in ['extract','lean','link','audit','inspect','kani']}
assert counts['extract']<=2 and sum(counts[k] for k in ['lean','link','audit','inspect'])<=50 and counts['kani']<=50
report=dict(status='LOCAL_CHECKS_PASS_CONCRETE_ROWS_PENDING',candidate_roots=[],credited_rows=0,own_theorems=len(audited),raw_audits=audited,scope_counts=counts,input_objects=checks,compressed_pairs=pairs,scope_overlap='NMW_SCOPE_OVERLAP.json: procedural violation retained for lead review',rejected_attempts=[x['attempt'] for x in scopes if x['exit_status']!=0],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),no_shipped_changes=True,standard_axioms_only=True,remaining='NMW_REMAINING.md')
(E/'NMW_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='raw_audits'}))
