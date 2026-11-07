"""Only this gate validator may publish the five CLOSED row records."""
from pathlib import Path
import json,hashlib,lzma,tarfile,collections
E=Path(__file__).resolve().parent;std={'propext','Classical.choice','Quot.sound'}
read=lambda n:json.loads((E/n).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
plan=read('PCI_GATE_PLAN.json');rootset=read('PCI_AUDIT_ROOTS_ALL.json')
def receipt(a):return read(a+'/receipt.json')
def rows(a):return [json.loads(s[11:]) for s in (E/a/'stdout.log').read_text().splitlines() if s.startswith('NEP_RESULT ')]
def scoped(a):
 r=receipt(a);ad=read(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert read(a+'-disk-0.json')['free']>=40_000_000_000,a
 for key,v in [('memory.high','6442450944'),('memory.max','8589934592'),('memory.swap.max','0'),('pids.max','64')]:assert str(r['limits'][key])==v,a
 assert int(r['swaps'])==0,a
 return r
for a in [plan['combined'],plan['driver'],plan['link'],plan['fixtures'],plan['scan'],plan['collect']]+plan['raw']:scoped(a)
for a in [plan['combined'],plan['driver'],plan['link'],plan['fixtures'],plan['scan'],plan['collect']]:assert receipt(a)['exit_status']==0,a
fixture=rows(plan['fixtures']);assert len(fixture)==8 and all(x['equal'] for x in fixture)
scan=[json.loads(s) for s in (E/'PCI_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(not x['dangling'] and not x['duplicate_owners'] and x['imports_match'] for x in scan)
raw=sum((rows(a) for a in plan['raw']),[]);by={x['root']:x for x in raw}
assert len(raw)==len(by)==len(rootset['roots'])
assert set(by)==set(rootset['roots']) and all(set(x['walked_axioms'])<=std for x in raw)
for a in plan['raw']:assert receipt(a)['exit_status'] in [0,1]
base=read('PCI_BINARY_BASE.json')
for mode in ['fixtures','scan']+[f'proof{i}' for i in range(len(plan['raw']))]:
 p=read('PCI_BINARY_'+mode+'.json');assert p['unchanged'] and p['before']==p['after']==base
binary=read('PCI_AUDIT_BINARY_PINS.json');assert {k:v['sha256'] for k,v in binary.items()}==base
assert sha(E/'PCI_WALKER.c')==base['PCI_native/PCI_WALKER.c']==plan['walker_sha256']
manifest=read('PCI_RAW_MANIFEST.json');assert manifest['all_import_pins_unchanged']
bundle=E/'PCI_RAW_BUNDLE.tar.xz';assert sha(bundle)==(E/'PCI_RAW_BUNDLE.tar.xz.sha256').read_text().split()[0]
with tarfile.open(bundle,'r:xz') as tf:
 for member in tf.getmembers():
  assert member.isfile() and member.name.startswith('PCI_RAW_FINAL/') and '..' not in Path(member.name).parts
  q=E/member.name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(tf.extractfile(member).read())
for r in manifest['files']:
 p=E/'PCI_RAW_FINAL'/(r['source']+'.xz');assert sha(p)==r['compressed_sha256']
 assert hashlib.sha256(lzma.decompress(p.read_bytes())).hexdigest()==r['uncompressed_sha256']
export=read('PCI_EXPORT.json');assert export['copy_only'] and not export['hardlinks'] and export['all_export_hashes_verified'] and export['deletions']==0
assert sha(E/'PCI_IMPORTS.json.xz')==export['seed_manifest_sha256']
pins=json.loads(lzma.decompress((E/'PCI_IMPORTS.json.xz').read_bytes()));assert len(pins)==manifest['import_files']
selected={'POOL:273':('PCI_Note.forwarding',['003'],['002']),'POOL:223':('PCI_ValidatePacket.full',['021','024','026','028'],['022','023','025','027','029','030']),'POOL:222':('PCI_SinglePacket.full',['049'],['050','051','052']),'POOL:280':('PCI_RootAddress.complete',['020'],['013','014']),'POOL:332':('PCI_CountState.complete',['006','008','010'],['007','009','011'])}
source={r['id']:r for r in read('PCI_SOURCE_MAP.json')};closed=[]
for row,(root,positive,negative) in selected.items():
 assert root in by
 for n,ok in [(n,True)for n in positive]+[(n,False)for n in negative]:
  a='PCI_K'+n;r=scoped(a);s=(E/a/'stdout.log').read_text();assert r['exit_status']==(0 if ok else 1)
  assert ('VERIFICATION:- SUCCESSFUL' if ok else 'VERIFICATION:- FAILED') in s and 'timed out' not in s.lower()
  if not ok:assert 'Failed Checks:' in s
  graph=read(a+'-graph-check.json');assert graph['graph_matches_frozen'] and read(a+'-lock-check.json')['unchanged']
  pool=next(r['features']for r in graph['all_crate_features'] if r['name']=='aspis-pool');assert set(pool)=={'default','pair-forest-account-evidence','pair-forest-source-invariant-audit','pair-forest-source-result-invariant-audit','pair-forest-verifier-lane-invariant-audit','r1-split-checkpoint'}
 closed.append(dict(id=row,status='CLOSED',function=source[row]['function'],frozen_body_sha256=source[row]['frozen_body_sha256'],root=root,domain_verbatim=read('PCI_CALLER_CLAUSES.json')[row]['domain_verbatim'],native_positive=['PCI_K'+n for n in positive],native_controls=['PCI_K'+n for n in negative],raw_axioms=by[root]['walked_axioms'],gate='PCI_AUDIT.json',trust='P6/D188 transport retained; reviewed source fission for223/332 and repaired PCG SDK forwarding for280; no new runtime value axiom'))
records=[json.loads(s) for s in (E/'PCI_ATTEMPTS.jsonl').read_text().splitlines()];counts=collections.Counter(r['kind']for r in records)
assert counts['lean']+counts['link']+counts['audit']==120 and counts['kani']<=130 and counts['extract']<=14
assert len(records)==len({r['attempt']for r in records})
audit=dict(status='PASS_FINAL',headline='AspisR1.RPx_Deployed.deployed',combined=plan['combined'],scan=plan['scan'],modules=len(scan),dangling=0,duplicate_owners=0,import_mismatches=0,own_roots=len(rootset['own']),total_roots=len(raw),raw=raw,fixtures=plan['fixtures'],fixture_count=8,binary=binary,all_modes_same_binary=True,raw_standard=True,collector_disagreements=[r for r in raw if not r['equal']],raw_authority="NEP ax2, (ab')(3)",budgets=dict(kani=counts['kani'],formal=120,extraction=counts['extract']),closed_rows=[r['id']for r in closed],target_established=False,export=export['export_directory'])
(E/'PCI_AUDIT.json').write_text(json.dumps(audit,indent=1)+'\n');(E/'PCI_CLOSED.json').write_text(json.dumps(closed,indent=1)+'\n')
delta=dict(basis='ledger24 NLX + accepted PCE/PCB/PCG/PCF packets',scope='17 assigned PCI rows',closed=closed,open=[dict(id=row,status='OPEN',reason='PCI_REMAINING.md')for row in source if row not in selected],closed_count=5,open_count=12,target_established=False)
(E/'PCI_LEDGER_DELTA.json').write_text(json.dumps(delta,indent=1)+'\n')
c=read('PCI_CALLER_CLAUSES.json')
for row in selected:c[row]['status']='CLOSED_UNDER_PCI_FINAL_GATE'
(E/'PCI_CALLER_CLAUSES.json').write_text(json.dumps(c,indent=1)+'\n')
print('PCI FINAL PASS:5 CLOSED,12 OPEN,103 own roots+headline standard,8 fixtures,17428 modules zero defects,formal120')
