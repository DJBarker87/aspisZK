#!/usr/bin/env python3
"""Validate final focused receipts and record unchanged frozen source scope."""
import hashlib,json,pathlib,re,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
E=ROOT/'evidence/ports3-20261023'
L=ROOT/'docs/research/100bit-spend-path-20261013/lean'
BASE=json.loads((E/'source-body-inventory.json').read_text())['revision']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
run=lambda *a:subprocess.check_output(a,cwd=ROOT,text=True).strip()
receipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
accepted=[r for r in receipts if r['exit_status']==0]
latest={}
for r in accepted:
 for name in r['sources']:latest[name]=r
modules=sorted(L.glob('Port3_*.lean'))
for p in modules:
 assert p.name in latest,p.name
 r=latest[p.name]
 assert r['source_hashes'][p.name]==sha(p),p.name
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert r['swaps']=='0'
 assert r['deps_fingerprint']['selected_objects']
 assert 'sorryAx' not in '\n'.join(r['print_axioms'])
 for names in re.findall(r'axioms: \[([^\]]*)\]','\n'.join(r['print_axioms'])):
  assert set(names.split(', '))<={'propext','Classical.choice','Quot.sound'}
 text=p.read_text()
 assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option\s+(maxHeartbeats|maxRecDepth)',text,re.M),p.name
 for name in re.findall(r'^(?:private )?theorem\s+(\w+)',text,re.M):
  assert re.search(r'#print axioms\s+(?:[\w.]+\.)?'+re.escape(name)+r'\b',text),(p.name,name)
changed=run('git','diff','--name-only',BASE).splitlines()
assert all(p.startswith(('design/PORTS3-','evidence/ports3-','tools/ports3-')) or
 p.startswith('docs/research/100bit-spend-path-20261013/lean/Port3_') for p in changed),changed
assert len(receipts)<=100
assert len(list(E.glob('rust-*/receipt.json')))==1
sources=['Cargo.toml','Cargo.lock','crates/aspis-r1-cost-probe/src/candidate.rs',
 'crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/compact.rs',
 'programs/r1-cost-probe/src/r1_pool_adapter.rs']
for name in sources:
 assert (ROOT/name).read_bytes()==subprocess.check_output(['git','show',BASE+':'+name],cwd=ROOT),name
build=ROOT/'docs/research/100bit-spend-path-20261013/evidence/s10-repin3-20261023/build-manifest.json'
artifacts=[{'source_revision':b['actual_source_revision'],**b['comparison']} for b in json.loads(build.read_text())['builds']]
assert {a['sha256'] for a in artifacts}=={
 'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',
 '63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299',
 '121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
manifest={'schema':'focused-extractor-proof-packet-v1','base_revision':run('git','rev-parse',BASE),
 'audit_revision':run('git','rev-parse','HEAD'),'dirty_sources_pinned':True,
 'status':'partial concrete source/reference installation; unrestricted op8 substitution refuted; S2 target OPEN',
 'lean_actual_attempts':len(receipts),'lean_budget':100,'kani_runs':0,'kani_budget':60,
 'compiler_free_attempt_ids':[],'no_timeout_or_memory_kill':all(r['exit_status'] in [0,1] for r in receipts),
 'final_targets':{p.name:{'attempt':latest[p.name]['attempt'],'sha256':sha(p),
 'receipt':str((E/latest[p.name]['attempt']/'receipt.json').relative_to(ROOT))} for p in modules},
 'attempts':[{'attempt':r['attempt'],'exit':r['exit_status'],'wall_seconds':r['wall_seconds'],
 'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'source_revision':r['source_revision'],
 'source_hashes':r['source_hashes'],'print_axioms':r['print_axioms']} for r in receipts],
 'freeze':{'parameters':{'variant':'S2','queries':22,'split':10,'final_weights':64},
 'wire':{'stored_proof_bytes':57607,'verifier_checkpoint_bytes':1768,'account_prefix':688},
 'local_source_hashes':{p:sha(ROOT/p) for p in sources},
 'shipped_delta_from_base':[],'features_and_program_ids':'unchanged; inherited S10 per-mode commands and configuration',
 'lean_toolchain':'leanprover/lean4:v4.32.0; exact binary hash in each receipt',
 'sbf_toolchain':'inherited S10 platform-tools v1.52; no new SBF build',
 'native_rust_toolchain':'nightly-2026-06-01, exact cargo/rustc binary hashes and resolved lock in rust-001-tool-and-dependency-pins.json',
 'native_counterexample':json.loads((E/'rust-001/receipt.json').read_text()),
 'source_normalization_sha256':sha(E/'source-normalization.json'),
 'artifact_evidence':str(build.relative_to(ROOT)),'artifact_evidence_sha256':sha(build),
 'artifact_pins':artifacts,'artifact_validation':'inherited evidence only; no rebuild or fresh ELF hash claim',
 'change_assessment':'New isolated proof/tool/evidence and native counterexample only. No shipped source or ELF delta. Exact input class and retained native bridges are documented; no whole-nine dictionary or whole frozen2 closure claimed.'}}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'final_modules':len(modules),'native_counterexamples':1,'lean_attempts':len(receipts),'kani_runs':0,'shipped_delta':[],'status':'PASS'}))
