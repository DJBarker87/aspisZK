from pathlib import Path
import subprocess,os,json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-c474-20261029'); O=H/'bundle';R=H/'src'; C=R/'tools/r1-cost-probe'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(H/'native-target'))
env.pop('CARGO_ENCODED_RUSTFLAGS',None)
features='r1p-check,aspis-r1-cost-probe/ct-host-prover'
a=subprocess.run(['cargo','+1.94.1','tree','--locked','--offline','-e','features','--features',features,'--target','x86_64-unknown-linux-gnu'],cwd=C,env=env,capture_output=True,text=True,check=True)
(O/'client-cargo-tree-features.txt').write_text(a.stdout);assert 'insecure-spend-fixture' not in a.stdout
# Unit graph selects precisely the binary built by the production recipe.
env['RUSTFLAGS']='--cfg getrandom_backend="linux_raw" --check-cfg=cfg(getrandom_backend,values("linux_raw")) -C link-arg=-Wl,--threads=4'
cmd=['cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features',features,'--bin','devnet_spend','-Z','unstable-options','--unit-graph']
a=subprocess.run(cmd,cwd=C,env=dict(env,RUSTC_BOOTSTRAP='1'),capture_output=True,text=True,check=True);(O/'client-unit-graph.json').write_text(a.stdout)
graph=json.loads(a.stdout);assert len(graph['roots'])==1
assert graph['units'][graph['roots'][0]]['target']['name']=='devnet_spend'
assert all('insecure-spend-fixture' not in u['features'] for u in graph['units'])
assert any('aspis-r1-cost-probe' in u['pkg_id'] and 'ct-host-prover' in u['features'] for u in graph['units'])
(O/'client-resolved-features.json').write_text(json.dumps([dict(package=u['pkg_id'],target=u['target']['name'],features=u['features'],profile=u['profile']) for u in graph['units']],indent=2)+'\n')
subprocess.run(['sh','./build-client.sh'],cwd=C,env=env,check=True)
p=H/'native-target/client/devnet_spend';b=p.read_bytes()
(O/'client-build.json').write_text(json.dumps(dict(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path=str(p),recipe=(C/'build-client.sh').read_text(),toolchain=subprocess.check_output(['rustc','+1.94.1','-vV'],env=env,text=True),unit_graph_command=cmd,bootstrap_scope='graph-only; no bootstrap on production compilation',insecure_spend_fixture=False,ct_host_prover=True),indent=2)+'\n')
# Same manifest and lock as actual client, only register the unchanged audit binaries.
V=R/'tools/pv-c474-validation';s=(C/'Cargo.toml').read_text()+'''\n[[bin]]\nname = "pv-c474-differential"\npath = "../../crates/aspis-r1-cost-probe/examples/prover_rw_differential.rs"\n[[bin]]\nname = "pv-c474-fixture"\npath = "../../crates/aspis-r1-cost-probe/examples/prover_rw_gate.rs"\n''';(V/'Cargo.toml').write_text(s)
assert (C/'Cargo.lock').read_bytes()==(V/'Cargo.lock').read_bytes()
cmd=['cargo','+1.94.1','build','--profile','client','--locked','--offline','-j','4','--features',features,'--bin','pv-c474-differential','--bin','pv-c474-fixture']
subprocess.run(cmd,cwd=V,env=env,check=True)
a=subprocess.run(cmd+['-Z','unstable-options','--unit-graph'],cwd=V,env=dict(env,RUSTC_BOOTSTRAP='1'),capture_output=True,text=True,check=True);(O/'harness-unit-graph.json').write_text(a.stdout)
h=json.loads(a.stdout)
def units(g):return {(u['pkg_id'],u['target']['name'],u['mode']):u for u in g['units'] if 'bin' not in u['target']['kind']}
c,d=units(graph),units(h);assert c.keys()==d.keys();assert all(c[k]==d[k] or {x:y for x,y in c[k].items() if x!='dependencies'}=={x:y for x,y in d[k].items() if x!='dependencies'} for k in c)
(O/'harness-parity.json').write_text(json.dumps(dict(shared_units=len(c),identical_features_profiles=True,harnesses={name:dict(sha256=hashlib.sha256((H/'native-target/client'/name).read_bytes()).hexdigest(),bytes=(H/'native-target/client'/name).stat().st_size) for name in ['pv-c474-differential','pv-c474-fixture']}),indent=2)+'\n')
print('BUILD_FEATURE_GRAPH_HARNESS_PARITY_PASS',flush=True)
