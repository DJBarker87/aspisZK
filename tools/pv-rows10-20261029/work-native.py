from pathlib import Path
import json,hashlib,subprocess,os
D=Path('/home/dombarker/project-offloads/codex-pv-rows10-20261029');F=D.parent/'codex-pv-fscan-20261028/src';O=D.parent/'codex-pv-ownd-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((D/'source-pins.json').read_text());inputs=[]
for r in pins:
 if r['path'].endswith(('host_work.rs','native_workers.rs')):
  p=F/r['path'];assert sha(p)==r['sha256'];inputs.append(dict(path=str(p),sha256=sha(p)))
units=json.loads((O/'deployed-units.json').read_text());u=next(u for u in units if '#aspis-r1-cost-probe@' in u['package_id'] and u['target']['name']=='aspis_r1_cost_probe')
assert 'ct-host-prover' in u['features'] and 'public-work-trace' not in u['features']
cmd=['rustc','+1.94.1','--edition=2021','-O','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind',str(D/'work-native.rs'),'-o',str(D/'work-native')]
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH']);print('Expected time: small optimized source harness compilation/link, then range checks and public-sized worker maps',flush=True)
subprocess.run(cmd,env=env,check=True);q=subprocess.run([str(D/'work-native')],text=True,capture_output=True,check=True);print(q.stdout,flush=True)
r=dict(command=cmd,toolchain=subprocess.check_output(['rustc','+1.94.1','-Vv'],env=env,text=True),deployed_crate_unit=u,features_all_crates=units,profile='release opt-level3 debug_assertions=false overflow_checks=false panic=unwind',source_inputs=inputs,binary_sha256=sha(D/'work-native'),harness_sha256=sha(D/'work-native.rs'),stderr=q.stderr,result=json.loads(q.stdout),evidence_class='finite validation of original source in deployed-configuration source harness; not shipped-binary execution or a universal refinement',retained='V370, runtime spawn/join/panic, allocator rdea-1 and physical observation association')
(D/'work-native-result.json').write_text(json.dumps(r,indent=2)+'\n')
