"""Validate final committed metadata and source binding without replaying any native gate."""
from pathlib import Path
import json,hashlib,subprocess,sys
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-c474b-20261029'
load=lambda p:json.loads((E/p).read_text());sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
client=load('client-build.json');assert client['sha256']=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
assert client['bytes']==2281512 and '1.94.1' in client['toolchain']
assert client['recipe']==(R/'tools/r1-cost-probe/build-client.sh').read_text()
g=load('client-unit-graph.json');assert len(g['roots'])==1 and g['units'][g['roots'][0]]['target']['name']=='devnet_spend'
assert all('insecure-spend-fixture' not in u['features'] for u in g['units'])
assert any('ct-host-prover' in u['features'] and 'aspis-r1-cost-probe' in u['pkg_id'] for u in g['units'])
assert 'insecure-spend-fixture' not in (E/'client-cargo-tree-features.txt').read_text()
assert all(x in client['recipe'] for x in ['+1.94.1','--locked','--offline','--profile client'])
for p in ['elf-default-affinity4/comparison.json','elf-devnet/comparison.json','elf-pool/comparison.json']:
 x=load(p);assert x['exit']==0 and x['byte_identical'] and x['sha256']==x['expected']
assert load('fixed-fixture-comparison.json')['passed']
a=load('runtime-private/acceptance.json');assert len(a['runs'])==4 and all(r['accepted'] and r['duplicate_ledger_unchanged'] for r in a['runs'])
x=load('ct-decoding.json');assert x['evidence_class']=='instruction-trace comparison' and x['identical'] and x['binary_sha256']==client['sha256']
assert len(x['classes'])==2 and x['classes'][0]['steps']==x['classes'][1]['steps'] and len(x['classes'][0]['steps'])==9
assert load('signing-fixture.json')['byte_identical']
c=load('corpus-6000/pipeline-final.json');assert c['complete'] and c['passed'] and (c['completed_pairs'],c['fully_executed_proof_pairs'],c['rejected_prefix_pairs'],c['oracle_logged_pairs'])==(1000,600,100,4)
assert load('corpus-ledger-audit.json')['passed']
if (E/'timing/summary.json').exists():
 t=load('timing/summary.json');assert t['pairs']==10 and len(t['summary'])==2 and all(x['verdict']=='PASS' and x['groups']['all']['within_10_percent'] and x['under_15_seconds'] for x in t['summary']);release_ready=True
else:
 assert '--timing-pending' in sys.argv and load('timing-blocker.json')['status']=='BLOCKED BEFORE LAUNCH';release_ready=False
f=load('final-audit.json');assert f['gate_checks_passed']==release_ready and f['all_executed_gates_passed'] and f['keys_deleted']==0 and not f['release_pins_changed'] and not f['source_mismatches']
for x in load('changed-spans.json'):assert sha(R/x['path'])==x['sha256']
for p,h in load('expected-sources.json').items():
 if (R/p).is_file():assert sha(R/p)==h,p
for p in ['PATCH.diff','PATCH.incremental-from-19c9611220.diff']:
 subprocess.run(['git','apply','--reverse','--check',str(E/p)],cwd=R,check=True)
allowed_failures={'native73500','native73501','native73503','native73510'}
receipts=[]
for p in sorted(E.glob('native*/receipt.json')):
 x=json.loads(p.read_text());assert p.parent.name.startswith('native735')
 assert x['limits']==dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)
 assert x['exit']==(1 if p.parent.name in allowed_failures else 0),(p,x['exit'])
 assert x['wall'] and x['peak_rss_kib'] and x['swap']=='0'
 for name in ['admission-before.json','admission-launch.json','admission-barrier.json']:assert json.loads((p.parent/name).read_text())['allowed'] is True
 receipts.append(x)
assert 0<len(receipts)<=40
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
print(json.dumps(dict(artifact_validation_passed=True,release_ready=release_ready,native_scopes=len(receipts),Lean=0,Kani=0,client_sha256=client['sha256'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()),indent=2))
