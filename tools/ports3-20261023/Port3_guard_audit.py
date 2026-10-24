#!/usr/bin/env python3
"""Additive audit of the complement-rejection counterexamples; no proof replay."""
import hashlib,json,pathlib,subprocess
R=pathlib.Path(__file__).resolve().parents[2]; E=R/'evidence/ports3-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
r=json.loads((E/'rust-002/receipt.json').read_text())
assert r['exit_status']==0 and r['swaps']=='0'
assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert '--release' in r['command'] and r['env']['CARGO_PROFILE_RELEASE_OPT_LEVEL']=='3'
for f,h in r['source_hashes'].items():
 assert sha(E/'rust-002/sources'/f)==h
 assert sha(R/'tools/ports3-20261023'/f)==h
for f,h in r['deps_fingerprint']['source_snapshot_pins'].items():
 assert sha(R/f)==h,f
old=json.loads((E/'rust-001-tool-and-dependency-pins.json').read_text())
pins=json.loads((E/'rust-002-tool-and-dependency-pins.json').read_text())
assert all(pins[k]==v for k,v in old['tool_binary_pins'].items())
assert pins['resolved_lock']==old['resolved_lock']
log=(E/'rust-002/stdout.log').read_text()
assert '1 passed; 0 failed' in log
assert 'OUTSIDE provenance.next:' in log and 'OUTSIDE provenance.queriesBound:' in log
lean=list(E.glob('lean-*/receipt.json')); assert len(lean)==18
base=r['source_revision']
diff=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(f.startswith(('tools/ports3-20261023/','evidence/ports3-20261023/','design/PORTS3-')) for f in diff),diff
continuation={'schema':'ports3-guard-counterexample-v1','source_revision':base,
 'status':'complement rejection refuted; reached-domain native writer equality OPEN; S2 target not yet established',
 'target':r['command'],'exit_status':r['exit_status'],'wall_seconds':r['wall_seconds'],
 'peak_rss_kib':r['peak_rss_kib'],'swaps':r['swaps'],'limits':r['limits'],
 'print_axioms':r['print_axioms'],'lean_attempts':len(lean),'lean_budget':100,'kani_runs':0,'kani_budget':60,
 'native_counterexample_jobs':2,'source_hashes':r['source_hashes'],
 'receipt':'evidence/ports3-20261023/rust-002/receipt.json',
 'source_validation':'evidence/ports3-20261023/rust-002-source-validation.json',
 'tool_pins':'evidence/ports3-20261023/rust-002-tool-and-dependency-pins.json',
 'source_change_assessment':'Isolated test/tool/evidence only. No shipped source, parameter, feature, wire or ELF change. Historical ELF pins reused, not rebuilt. No new theorem or native equivalence certificate.',
 'new_assumptions':[],'discharged_native_port_obligations':[],
 'remaining':'Derive all provenance facts from same installed TX1 prefix; prove guarded native writer equality without a complement rejection claim, then ordered remaining rows.'}
(E/'continuation-guard.json').write_text(json.dumps(continuation,indent=2)+'\n')
manifest=json.loads((E/'manifest.json').read_text())
manifest['continuation_guard']={'receipt_manifest':'evidence/ports3-20261023/continuation-guard.json','sha256':sha(E/'continuation-guard.json')}
(E/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS: two native complement counterexamples; 18 Lean / 0 Kani; capped optimized run; no shipped delta')
