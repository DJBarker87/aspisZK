#!/usr/bin/env python3
"""Audit all seventeen actual-SDK first-entry coordinate gates and reused index
coverage, without replaying any solver/Lean target. Entry-only, not whole S2.
"""
from pathlib import Path
import json,hashlib,re,subprocess,tempfile,tomllib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021';E=B/'sdk-first-entry-v2'
load=lambda p:json.loads(p.read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,d in load(E/'manifest.json')['files'].items():assert sha(E/n)==d,n
assert not any(p.suffix in ['.out','.o','.rlib','.olean','.llbc'] for p in E.rglob('*'))
q=load(E/'qualification.json');assert not q['pending'] and len(q['accepted'])==17
base=(B/'sdk-native-frame-windows/sources/sdk-shared-prefix-v19/src/lib.rs').read_text().split('#[cfg(kani)] mod proofs')[0]
accepted=[];domains=[]
for root,windows in [(0,range(15)),(1,[None]),(2,[None])]:
 for w in windows:
  v=f'first-entry-root{root}'+(f'-window{w}' if w is not None else '')+'-v2';tag='sdk-'+v;cg='sdk-shared-prefix-codegen-'+v;P=E/'sources'/v;case=E/'cases'/v
  i=load(E/(tag+'-input.json'));c=load(E/(cg+'-input.json'));r=load(E/'receipts'/tag/'receipt.json');a=load(case/'entry-audit.json');cut=load(P/'source-cut.json')
  assert r['exit_status']==10 and r['swaps']==0 and r['limits']['memory.swap.max']=='0' and int(r['limits']['memory.max'])==8*1024**3
  assert i['source_scope']=='native_first_entry_only' and i['source_sha256']==c['source_sha256']==cut['source_sha256']==sha(P/'src/lib.rs')
  assert load(E/(cg+'-dependency-postcheck.json'))['unchanged']=={n:True for n in c['local_dependency_source_pins']}
  for name,pin in c['local_dependency_source_pins'].items():
   for rel,d in pin['files'].items():assert sha(E/'dependencies'/name/rel)==d
  assert i['harness_metadata']['attributes']['kind']=='Proof'
  assert not any('AccountInfo::' in str(x) or 'sdk_live_models' in str(x) for x in i['harness_metadata']['attributes']['stubs'])
  assert '--property' not in i['commands'][-1] and '--unwinding-assertions' in i['commands'][-1]
  assert cut['events']==['first/tx1 entry only'] and cut['observer_root']==root and cut['observer_window']==w
  source=(P/'src/lib.rs').read_text();assert source.split('#[cfg(kani)] mod proofs')[0]==base
  assert 's126_keep_coupled_cmp.value=Some(s126_coupled_cmp)' in source and 's126_keep_coupled_cmp:GhostStorage<' in source
  assert 'fn observer()->verifier::Observer {None}' in source
  assert source.count('frame_probe();')==1 and source.count('kani::cover!(')==2
  assert 'kani::assume(false);\n Ok(Vec::new())' in source
  sdk=[p for p in tomllib.loads((P/'Cargo.lock').read_text())['package'] if p['name']=='solana-account-info'];assert len(sdk)==1 and sdk[0]['version']=='2.3.0'
  props=[p for x in load(case/'property-inventory.json') for p in x.get('properties',[])];expected={p['name']:p for p in props};assert len(expected)==len(props)
  rows=[];current=None;block=[]
  for line in (case/'all-properties.log').read_text().splitlines():
   end=line.find('] ') if line.startswith('[') else -1
   while end>=0 and line[1:end] not in expected:end=line.find('] ',end+2)
   if end>=0:assert current is None;current=line[1:end];block=[line[end+2:]]
   elif current is not None:block.append(line)
   if current is not None:
    match=re.fullmatch(r'(.*): (SUCCESS|FAILURE|UNKNOWN|UNREACHABLE|NOT CHECKED|ERROR)','\n'.join(block),re.S)
    if match:rows.append(dict(property=current,description=match[1],status=match[2]));current=None;block=[]
  assert current is None and rows==load(case/'properties-complete.json')
  actual={p['property']:p for p in rows};assert len(actual)==len(rows) and actual.keys()==expected.keys()
  covers=[p['name'] for p in props if p['class']=='cover'];assert len(covers)==2
  assert all(p['status']==('FAILURE' if p['property'] in covers else 'SUCCESS') for p in rows)
  assert a['noncover_successes']==len(props)-2
  with tempfile.TemporaryDirectory() as d:
   out=Path(d)/'entry';subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-native-first-entry.py'),str(out),str(root),*([str(w)] if w is not None else [])],check=True)
   for rel in ['src/lib.rs','Cargo.toml','source-cut.json']:assert (out/rel).read_bytes()==(P/rel).read_bytes(),(v,rel)
  domain=re.sub(r' let selected_root:usize=\d+;\n.*? let lengths=', ' let selected_root:usize=ROOT;\n let lengths=',source,flags=re.S);domains.append(domain)
  accepted.append(dict(target=tag,checks=len(props)-2,covers=2,wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps']))
assert len(set(domains))==1,'All source input/child/argument/scalar domains must match; only coordinate selector differs.'
coverage=B/'sdk-native-frame-windows/receipts/sdk-native-frame-coverage-v2';receipt=load(coverage/'receipt.json');assert receipt['exit_status']==0 and receipt['swaps']==0
log=(coverage/'stdout.log').read_text();assert 'sorryAx' not in log and 'axiom' in log
assert (coverage/'source.lean').read_bytes()==(R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/S2SdkNativeFrameCoverageV1.lean').read_bytes()
print(json.dumps(dict(accepted=accepted,reused_index_coverage_source_sha256=sha(coverage/'source.lean'),qualification=__doc__+' Generic index/list theorem unchanged; complete source certificate/execution instantiation and actual child/gate/scan/runtime/oracle/continuation joins remain.'),indent=2))
