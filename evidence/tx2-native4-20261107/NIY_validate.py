"""Own strict final evidence validator; no ledger promotion by local facets."""
from pathlib import Path
import json,hashlib,re,lzma,subprocess
E=Path(__file__).resolve().parent
load=lambda p:json.loads((E/p).read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('NIY_[LKE][0-9][0-9][0-9]/receipt.json'))]
by={r['attempt']:r for r in receipts};k=[r for r in receipts if r['kind']=='kani'];l=[r for r in receipts if r['attempt'].startswith('NIY_L')];ex=[r for r in receipts if r['kind']=='extract']
assert len(k)<=100 and len(l)<=100 and len(ex)<=1
for r in receipts:
 a=r['attempt'];ad=load(a+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert str(r['swaps'])=='0',a
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
 if r['kind']=='kani':
  g=load(a+'-graph-check.json');lock=load(a+'-lock-check.json');source=load(a+'-source-check.json')
  assert g['graph_matches_frozen'] and not g['new_package_tuples'] and not g['edge_errors'] and not source['errors'],a
  assert lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef',a
  c=load(a+'.json');env=c['env'];assert env['CARGO_NET_OFFLINE']=='true' and env['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and '-Copt-level=3' in env['RUSTFLAGS'],a
  assert env['CARGO_TARGET_DIR'].endswith('/codex-cx-tx2-native4-20261107/NIY_target'),a
  assert '--locked' not in c['native_command'] and '--harness-timeout' in c['native_command'] and '90s' in c['native_command'],a
  features={p['name']:set(p['features']) for p in g['all_crate_features']}
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe'],a
  assert {'r0','pool-v1-kernel'}<=features['aspis-statement'],a
  assert sum(x.startswith('pool-v1-pair-forest-') for x in features['aspis-statement'])==12,a
 if r['kind']=='lean':assert '-M7000' in r['command'] and len([x for x in r['command'] if x.endswith('.lean')])==1,a
# Source-only forbidden constructs are checked on all own new proof modules, not retained failure logs.
for p in E.glob('NIY_*.lean'):
 if p.name in ['NIY_Driver.lean','NIY_ProofDriver.lean']:continue
 assert not re.search(r'\b(?:sorry|admit|native_decide)\b|set_option\s+(?:maxRecDepth|maxHeartbeats)|^\s*axiom\s',p.read_text(),re.M),p.name
for n,s in load('NIY_NATIVE_INPUTS.json').items():
 if '/NIY_' not in n:continue
 assert not re.search(r'\bstatic\s+mut\b|\bstatic\s+\w+\s*:\s*(?:Cell|RefCell|UnsafeCell|Atomic)|Option\s*<\s*fn',s),n
mods=load('NIY_MODULES.json')['selected']
for m in mods:
 r=json.loads((E/m['receipt']).read_text());p=E/(m['module']+'.lean')
 assert r['exit_status']==0 and sha(p)==m['source_sha256']==r['source_hashes']['NIY_generated/'+m['module']+'.lean'],m['module']
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   axioms={x.strip() for x in line.rsplit('[',1)[1].rstrip(']').split(',') if x.strip()};assert axioms<=standard,line
matrix=load('NIY_NATIVE_MATRIX.json');qualified=[];partial=[]
for row in matrix:
 ok=True
 for mode in ['positive','negative','rename']:
  a=row.get(mode)
  if not a:ok=False;continue
  r=by[a];raw=(E/a/'stdout.log').read_text();limit=any(s in raw.lower() for s in ['cbmc timed out','out of memory','excessive memory'])
  good=(r['exit_status']!=0 and 'VERIFICATION:- FAILED' in raw and not limit and 'assertion' in raw.lower()) if mode=='negative' else (r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in raw)
  ok=ok and good
 if ok:
  # Same actual source manifest and complete crate features across the three configurations.
  names=[row[m] for m in ['positive','negative','rename']]
  source_hash=[by[a]['source_hashes']['NIY_SOURCE_PINS.json'] for a in names];assert len(set(source_hash))==1,row['family']
  feat=[load(a+'-graph-check.json')['all_crate_features'] for a in names];assert feat[0]==feat[1]==feat[2],row['family']
  qualified.append(row['family'])
 else:partial.append(row['family'])
# Timeouts cannot be counted as controls or passes.
for a in ['NIY_K035','NIY_K051']:
 assert by[a]['exit_status']!=0 and 'CBMC timed out' in (E/a/'stdout.log').read_text(),a
 assert not any(row.get('negative')==a for row in matrix),a
assert load('NIY_HEADER_QUALIFICATION.json')['same_crate_features'] is True
roots=[x for g in load('NIY_AUDIT_ROOTS.json')['groups'] for x in g]
audit=json.loads((E/'NIY_audit/all/proof0.json').read_text()) if (E/'NIY_audit/all/proof0.json').exists() else None
assert audit is not None,'raw ax2 gate missing'
walk=[]
for p in (E/'NIY_audit/all').glob('*.json'):
 x=json.loads(p.read_text());assert x['exit_status']==0
 for r in x['results']:
  assert r['equal'] and set(r['walked_axioms'])<=standard and set(r['collect_axioms'])<=standard,r['root']
  walk.append(r['root'])
assert sorted(walk)==sorted(roots),(len(walk),len(roots))
fix=json.loads((E/'NIY_audit/fixtures/fixtures.json').read_text());assert fix['exit_status']==0 and len(fix['results'])==8
for r in fix['results']:
 assert r['equal'];assert bool(r['walked_axioms'])==r['root'].startswith('NEP_Planted'),r['root']
scan=[json.loads(s) for s in (E/'NIY_LOADED_scan.jsonl').read_text().splitlines()]
assert scan and all(r['imports_match'] and not r['dangling'] and not r['duplicate_owners'] for r in scan)
assert any(r['module']=='NIY_COMBINED_IMPORT' for r in scan)
assert load('NIY_WALKER_PINS.json')['walker_byte_identical'] is True
assert load('NIY_SOURCE_VERIFICATION.json')['status']=='PASS' and load('NIY_RETENTION.json')['status']=='PASS'
assert len(ex)==1 and ex[0]['exit_status']==0 and load('NIY_EXTRACT_PINS.json')['source_restored'] and load('NIY_EXTRACT_PINS.json')['target_resolves']
base_path=E.parent/'ledger12-20261107/NIR_LEDGER.json.xz';base=json.loads(lzma.decompress(base_path.read_bytes()));delta=load('NIY_LEDGER_DELTA.json');closed=load('NIY_CLOSED.json')
assert delta['baseline_compressed_sha256']==sha(base_path) and not delta['rows'] and not delta['edges']
assert delta['counts_before']==delta['counts_after']==base['counts'] and not closed['closed_rows'] and not closed['closed_edges']
assert not delta['security_target_established'] and not delta['trust_rows_added'] and not delta['trust_rows_removed']
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024],'>20MiB evidence file'
result=dict(status='PASS',model_transport='NIY_TailPort.source / NIY_ResumePort.source',native_rows_closed=0,edges_closed=0,qualified_local_families=qualified,partial_or_unattempted=partial,raw_roots=len(walk),fixtures=8,scan_modules=len(scan),attempts=dict(kani=len(k),lean_support=len(l),extraction=len(ex)),target_established=False)
(E/'NIY_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['qualified_local_families','partial_or_unattempted']}))
