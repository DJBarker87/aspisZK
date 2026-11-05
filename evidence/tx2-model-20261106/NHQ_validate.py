"""Validate selected conditional model evidence; never promote an OPEN row."""
from pathlib import Path
import json,re,hashlib,lzma
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
selected={'NHQ_Tx2CommonModel':'NHQ_L011','NHQ_Tx2AuthModel':'NHQ_L029','NHQ_FinishRelationModel':'NHQ_L021','NHQ_PacketPorts':'NHQ_L014','NHQ_RoundDomain':'NHQ_L020','NHQ_WeightPort':'NHQ_L025','NHQ_FinishPackets':'NHQ_L022','NHQ_FinishFrames':'NHQ_L026','NHQ_QueryFrame':'NHQ_L028','NHQ_COMBINED_IMPORT':'NHQ_L031'}
std={'propext','Classical.choice','Quot.sound'}
pack=json.loads((E/'NHQ_PACK.json').read_text())
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NHQ_[LE]???/receipt.json'))]
for r in receipts:
 a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
 assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 assert str(r['swaps'])=='0',a
 assert r['source_revision'] and r['source_hashes'] and r['deps_fingerprint'],a
 assert all((E/a/n).exists() for n in ['stdout.log','time.log']),a
 for name,digest in r['source_hashes'].items():
  p=E/a/'sources'/name
  if not p.exists():
   ref=pack[str(p.relative_to(E))];assert ref['sha256']==digest
   p=E/ref['canonical']
  assert sha(p.read_bytes())==digest,(a,name)
for n,a in selected.items():
 r=json.loads((E/a/'receipt.json').read_text());assert r['exit_status']==0,a
 p=E/(n+'.lean');assert sha(p.read_bytes())==r['source_hashes']['NHQ_generated/'+n+'.lean'],n
 assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b',p.read_text()),n
 for t in re.findall(r'^theorem (\w+)',p.read_text(),re.M):
  assert '#print axioms '+t in p.read_text(),(n,t)
roots=json.loads((E/'NHQ_AUDIT_ROOTS.json').read_text())['groups'][0]
raw=json.loads((E/'NHQ_audit/batch0/proof0.json').read_text());fixtures=json.loads((E/'NHQ_audit/fixtures/fixtures.json').read_text())
assert raw['exit_status']==0 and len(raw['results'])==len(roots)==29
assert {r['root'] for r in raw['results']}==set(roots)
assert all(r['equal'] and set(r['walked_axioms'])<=std for r in raw['results'])
assert fixtures['exit_status']==0 and len(fixtures['results'])==8
assert all(r['equal'] for r in fixtures['results'])
assert all(r['walked_axioms'] for r in fixtures['results'][:4])
assert all(not r['walked_axioms'] for r in fixtures['results'][4:])
for a in ['NHQ_L033','NHQ_L034','NHQ_L035']:
 pin=json.loads((E/a/'NHQ_ProofDriver_BINARY_PIN.json').read_text());assert pin==json.loads((E/'NHQ_L033/NHQ_ProofDriver_BINARY_PIN.json').read_text())
scan=json.loads((E/'NHQ_audit/scan/scan.json').read_text());assert scan['exit_status']==0
rows=[json.loads(l) for l in (E/'NHQ_LOADED_scan.jsonl').read_text().splitlines()]
assert rows and all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in rows)
closure=lzma.decompress((E/'NHQ_CLOSURE_PINS.json.xz').read_bytes());assert sha(closure)==(E/'NHQ_CLOSURE_PINS.json.sha256').read_text().strip()
assert json.loads(closure)['modules']==len(rows)
identity=json.loads((E/'NHQ_SHIPPED_IDENTITY.json').read_text());assert all(x['byte_identical'] for x in identity.values())
delta=json.loads((E/'NHQ_LEDGER_DELTA.json').read_text());assert not delta['promotions'] and all(x['status_after']=='OPEN' for x in delta['rows'])
assert all(p.stat().st_size<=20*1024*1024 for p in E.rglob('*') if p.is_file())
assert not list(E.rglob('__pycache__'))
summary=dict(status='PASS for retained conditional model evidence; requested fresh emission INCOMPLETE',selected=selected,raw_roots=len(roots),standard_axioms_only=True,fixtures=8,scan_exit=0,scan_modules=len(rows),scan_declarations=sum(r['declarations'] for r in rows),scan_edges=sum(r['edges'] for r in rows),compatible_replicas=sum(len(r['cached_replicas']) for r in rows),promotions=0,extraction_invocations=2,fresh_emissions=0,actual_lean_support_scopes=sum(r['kind']!='extract' for r in receipts),conservative_lean_support_allocations=39,lean_budget=80,kani=0,wall_seconds=sum(r['wall_seconds'] for r in receipts),peak_rss_kib=max(int(r['peak_rss_kib']) for r in receipts),swap=0,failed_attempts=[r['attempt'] for r in receipts if r['exit_status']!=0],prelaunch_exclusions=['NHQ_L001','NHQ_L024','NHQ_L030'],quarantined_kani=[],suspended_kani=[])
(E/'NHQ_AUDIT.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
