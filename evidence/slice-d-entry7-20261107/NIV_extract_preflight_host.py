from pathlib import Path
import json,hashlib,subprocess,time,os
import NIV_stage as stage
B=Path(__file__).resolve().parent;S=B/'NIV_src';T=B/'NIV_NHR_target';out=B/'NIV_entry_preflight';out.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
warm=json.loads((B/'NIV_WARM_RESULT.json').read_text());assert warm['exit']==0 and warm['lock_unchanged'] and warm['source_unchanged']
assert os.environ['CARGO_TARGET_DIR']==str(T)
cmd=['python3',str(B/'NIV_stage.py'),'--check','--function','entry','--workspace',str(S),'--out',str(out)]
r=subprocess.run(cmd);assert r.returncode==0
opts=['python3',str(B/'NIV_stage.py'),'--options','--function','entry','--workspace',str(S),'--out',str(out),'--opacity',str(B/'NIV_OPACITY.json')]
r=subprocess.run(opts);assert r.returncode==0
options=json.loads((out/'NHR_OPTIONS.json').read_text());assert options['root']=='crate::process_r1_cost_probe_instruction' and options['root_features']=='pool-adapter,private-leaf-salts'
host=next(l.split(':',1)[1].strip() for l in warm['toolchain'].splitlines() if l.startswith('host:'))
filtered=['/home/dombarker/.cargo/bin/cargo','+1.94.1','metadata','--manifest-path',str(S/'programs/r1-cost-probe/Cargo.toml'),'--locked','--offline','--format-version','1','--features','pool-adapter,private-leaf-salts','--filter-platform',host]
r=subprocess.run(filtered,capture_output=True,text=True);assert r.returncode==0,r.stderr
(out/'filtered_metadata.stdout').write_text(r.stdout);(out/'filtered_metadata.stderr').write_text(r.stderr)
meta=json.loads(next(l for l in r.stdout.splitlines() if l.startswith('{')));pkgs={p['id']:p for p in meta['packages']};nodes={n['id']:n for n in meta['resolve']['nodes']}
root=next(i for i,p in pkgs.items() if p['name']=='aspis-r1-cost-probe-program');seen=set()
def visit(i):
 if i in seen:return
 seen.add(i)
 for d in nodes[i]['deps']:
  if any(k['kind'] in (None,'build') for k in d['dep_kinds']):visit(d['pkg'])
visit(root)
all_artifacts=[p for p in T.rglob('*') if p.is_file() and p.suffix in ['.rlib','.rmeta','.so']]
# Cargo metadata unifies optional workspace features; use the actual release
# unit graph (query only, no compilation) to identify the warmed build units.
unit_cmd=warm['command']+['-Z','unstable-options','--unit-graph']
unit_env={**os.environ,'RUSTUP_TOOLCHAIN':'nightly-2026-09-17','RUSTFLAGS':'-Zthreads=1 -C link-arg=-Wl,--threads=1'}
u=subprocess.run(unit_cmd,capture_output=True,text=True,env=unit_env);assert u.returncode==0,u.stderr
(out/'unit_graph.stdout').write_text(u.stdout);(out/'unit_graph.stderr').write_text(u.stderr)
units=json.loads(next(l for l in u.stdout.splitlines() if l.startswith('{')))
missing=[];artifacts=[]
for unit in units['units']:
 target=unit['target'];kinds=set(target['kind']);name=target['name'].replace('-','_')
 if 'proc-macro' in kinds:matches=[p for p in all_artifacts if p.suffix=='.so' and (p.name.startswith('lib'+name+'-') or p.name=='lib'+name+'.so')]
 elif kinds.intersection({'lib','rlib','cdylib','staticlib','dylib'}):matches=[p for p in all_artifacts if p.suffix in ['.rlib','.rmeta'] and (p.name.startswith('lib'+name+'-') or p.name in ['lib'+name+'.rlib','lib'+name+'.rmeta'])]
 else:continue
 if not matches:missing.append(dict(package=unit['pkg_id'],target=name,kinds=sorted(kinds),features=unit['features']))
 for p in matches:
  assert p.resolve().is_relative_to(T.resolve()),('cache escaped owned target',p)
  artifacts.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
assert not missing,('cold deployed dependency',missing)
t=time.monotonic();version=subprocess.run([str(stage.TOOLROOT/'charon'),'--help'],capture_output=True,text=True);startup=time.monotonic()-t
assert version.returncode==0 and startup<180,(version.returncode,version.stderr)
report=dict(status='PASS_WARM_PINNED_PREFLIGHT',allowed=True,extraction_launched=False,warm_wall=warm['wall'],warm_graph_sha256=sha(B/'NIV_warm/NHR_GRAPH_CHECK.json'),current_graph_sha256=sha(out/'NHR_GRAPH_CHECK.json'),filtered_metadata_command=filtered,unit_graph_command=unit_cmd,unit_graph_sha256=sha(out/'unit_graph.stdout'),actual_build_units=len(units['units']),host=host,selected_packages=len(seen),missing=missing,artifacts=artifacts,cache=str(T),charon_startup_seconds=startup,charon_startup_probe='--help (pinned Charon has no --version flag)',charon_help_sha256=hashlib.sha256(version.stdout.encode()).hexdigest(),options=options,stager_sha256=sha(B/'NIV_stage.py'),tool_pins=stage.PINS,source_revision=stage.REV,timeout=180,limitation='Complete deployed cache plus pinned tool startup demonstrated; translation may still fail within the unchanged180s limit. No extraction yet.')
(B/'NIV_EXTRACTION_PREFLIGHT.json').write_text(json.dumps(report,indent=1)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['artifacts','options']}),flush=True)
