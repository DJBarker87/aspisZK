"""Validate actual receipts, retained inputs, controls and own proof audits."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess,collections
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
idx=json.loads((E/'NMV_INPUTS.json').read_text());checks=0
for h,x in idx['objects'].items():
 p=E/x['path'];assert sha(p.read_bytes())==x['archive_sha256'];raw=lzma.decompress(p.read_bytes());assert len(raw)==x['bytes'] and sha(raw)==h;checks+=1
entries=[json.loads(l) for l in (E/'NMV_ATTEMPTS.jsonl').read_text().splitlines()]
scopes=[x for x in entries if 'full_receipt' in x];assert len({x['attempt'] for x in scopes})==len(scopes)
for x in scopes:
 rc=json.loads((E/x['full_receipt']).read_text());assert sha((E/x['full_receipt']).read_bytes())==x['full_receipt_sha256']
 assert rc['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 assert float(rc['swaps'])==0
 ad=json.loads((E/(rc['attempt']+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed'] is True
 for p,h in rc['source_hashes'].items():assert idx['attempts'][rc['attempt']][p]==h
 if rc['kind'] in ['lean','support']:assert '-M7000' in rc['command']
for l in (E/'NMV_DISK.jsonl').read_text().splitlines():assert json.loads(l)['free_bytes']>=40_000_000_000
pairs=0
for p in E.rglob('*.sha256'):
 target=p.with_name(p.name.removesuffix('.sha256')+'.xz')
 if target.exists():assert sha(lzma.decompress(target.read_bytes()))==p.read_text().strip();pairs+=1
wanted=json.loads((E/'NMV_AUDIT_ROOTS.json').read_text())['roots'];audited={};fixtures=[]
allowed={'propext','Classical.choice','Quot.sound'}
for p in (E/'NMV_audit').rglob('*.json'):
 d=json.loads(p.read_text());assert d['exit_status']==0
 if d['target']=='fixtures':fixtures.extend(d['results']);continue
 for row in d['results']:
  assert row['equal'] is True and set(row['walked_axioms'])<=allowed and set(row['collect_axioms'])<=allowed
  assert row['root'] not in audited;audited[row['root']]=dict(row,receipt=str(p.relative_to(E)))
assert set(audited)==set(wanted),(set(wanted)-set(audited),set(audited)-set(wanted))
assert len(fixtures)==8
for row in fixtures:
 assert row['equal'] is True
 if row['root'].startswith('NEP_Planted.'):
  assert len(row['walked_axioms'])==1 and row['walked_axioms']==row['collect_axioms']
  assert row['walked_axioms'][0].startswith('NEP_Planted.')
 else:assert not row['walked_axioms'] and not row['collect_axioms']
modules=json.loads((E/'NMV_EXPORT_MODULES.json').read_text());latest={}
for rc in scopes:
 if rc['kind']=='lean' and rc['exit_status']==0:latest[rc['module']]=rc
for m in modules:
 p=E/(m+'.lean');assert p.exists();h=sha(p.read_bytes());assert h in latest[m]['source_hashes'].values(),m
 for line in re.findall(r'^theorem (\w+)',p.read_text(),re.M):assert '#print axioms '+line in p.read_text(),(m,line)
 code=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);code=re.sub(r'--[^\n]*','',code)
 assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',code),m
controls={
 'NMV_K019':0,'NMV_K026':1,'NMV_K027':0,'NMV_K028':1,
 'NMV_K029':0,'NMV_K030':1,'NMV_K031':1,'NMV_K032':1,'NMV_K033':0,'NMV_K034':1}
for a,status in controls.items():
 rc=json.loads((E/a/'receipt.json').read_text());assert rc['exit_status']==status
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 assert 'VERIFICATION:- '+('SUCCESSFUL' if status==0 else 'FAILED') in log
 assert 'unwinding assertion' not in log
 graph=json.loads((E/(a+'-graph-check.json')).read_text());assert graph['graph_matches_frozen']
 lock=json.loads((E/(a+'-lock-check.json')).read_text());assert lock['unchanged']
 assert graph['all_crate_features']
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
counts=dict(collections.Counter(x['kind'] for x in scopes))
formal=sum(counts.get(k,0) for k in ['lean','support','link','audit','inspect'])
assert formal<=250 and counts.get('kani',0)<=60 and counts.get('extract',0)==2
shipped=subprocess.check_output(['git','diff','--name-only','68730c8ae22','--','crates','programs','Cargo.lock'],text=True).splitlines();assert not shipped
report=dict(status='SUPPORT_GATES_PASS_ACTUAL_WRAPPER_ROOTS_OPEN',candidate_roots=[],credited_rows=0,own_theorems=len(audited),raw_audits=audited,scope_counts=counts,formal_scopes=formal,actual_extractions=1,extract_scopes=2,extraction_note='L001 argparse rejected before extraction; L002 actual extraction',input_objects=checks,compressed_pairs=pairs,fixtures=len(fixtures),scope_overlap='Inherited NMV_SCOPE_TIMES.json: L012/K006 overlap retained for lead review',retired_family_late_attempt='Inherited K025 near-duplicate retained in NMV_FINDINGS.md',failed_or_negative_attempts=[x['attempt'] for x in scopes if x['exit_status']!=0],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),no_shipped_changes=True,standard_axioms_only=True,remaining='NMV_REMAINING.md')
(E/'NMV_AUDIT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='raw_audits'}))
