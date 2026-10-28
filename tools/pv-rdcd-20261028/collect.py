from pathlib import Path
import subprocess,json,shlex,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028';D='/home/dombarker/project-offloads/codex-pv-rdcd-20261028'
files=['deployed-client-features.json','source-freeze-result.json','zeroize190-complete-structural.json','preflight-results.json','external-overlay.json','env-J.json','typed-reached-static/typed-decisions.json','typed-reached-static/root-audit.json']
for n in ['encoder','circle','weights','bytes','arithmetic','leaves','focused-leaves','statement-eq']:
 for f in ['inputs.json','Cargo.toml.txt','fixture.rs.txt']:files.append('classify-project-'+n+'/'+f)
for f in ['inputs.json','Cargo.toml','Cargo.lock']:files.append('digest-fixture/'+f)
code='''from pathlib import Path
import json
D=Path(ROOT);print(json.dumps({f:(D/f).read_text() for f in FILES}))
'''.replace('ROOT',repr(D)).replace('FILES',repr(files))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
for f,s in json.loads(r.stdout).items():
 p=E/'captures'/f;p.parent.mkdir(exist_ok=True,parents=True);p.write_text(s)
q=subprocess.run(['scp','-q','dombarker@100.108.41.90:'+D+'/typed-reached-static/reached-audit.json.xz',str(E/'typed-reached-static.json.xz')]);assert q.returncode==0
# Native std/dep features are recorded even for read-only structural runs.
features=json.loads((E/'captures/deployed-client-features.json').read_text());profile=dict(name='release',opt_level=3,debug_assertions=False,overflow_checks=False,panic='unwind')
configuration=dict(artifact='devnet_spend',root='tools/r1-cost-probe',explicit_features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],toolchain='rustc1.94.1 e408947bfd200af42db322daf0fadfe7e26d3bd1',profile=profile,resolved_crates=[dict(package_id=x['package_id'],name=x['name'],features=x['features'],profile=x['profile']) for x in features])
for p in E.glob('*/receipt.json'):
 j=json.loads(p.read_text());j['deployed_configuration']=configuration
 suite=p.parent.name.removeprefix('native-')
 inputs=E/'captures'/('classify-project-'+suite)/'inputs.json'
 if inputs.exists():
  v=json.loads(inputs.read_text());j['actual_fixture_configuration']=dict(features=v['features'],profile=v['profile'],input_pins=v['input_pins']);q=inputs.with_name('fixture.rs.txt');j['compiled_fixture_sha256']=hashlib.sha256(q.read_bytes()).hexdigest()
 elif p.parent.name.startswith('native-zeroize'):
  v=json.loads((p.parent/'result.json').read_text());j['actual_fixture_configuration']={k:v[k] for k in ['toolchain','features','profile','checks']}
 elif p.parent.name=='native-digest':j['actual_fixture_configuration']=json.loads((E/'captures/digest-fixture/inputs.json').read_text())
 if j.get('module') and j.get('source_path'):
  src=R/j['source_path'];j['source_sha256']=hashlib.sha256(src.read_bytes()).hexdigest()
 j['rust_configuration_applicability']='Context for native source association; no Rust crate is compiled by a Lean or Python-only gate.'
 p.write_text(json.dumps(j,indent=2)+'\n')
print('Collected',len(files),'artifacts; added deployed graph/profile/toolchain to every existing scope receipt')
