from pathlib import Path
import hashlib,json,re,shlex,shutil,subprocess,tarfile
w=Path('/home/dombarker/project-offloads/aspis-r1-readonly-meta-20261016/runtime-check');o=w/'evidence-stage';o.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def put(p,rel):
 q=o/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 return {'member':rel,'source_path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)}
for n in ['inputs.json','inputs-harness-a.json','setup.json','setup-runtime.py','run-host.py','runtime-postflight.py']:
 put(w/n,n)
for p in sorted((w/'runs').rglob('*')):
 if p.is_file():put(p,str(p.relative_to(w)))
x=json.loads((w/'inputs.json').read_text())
for p,h in x['files'].items():assert sha(w/p)==h
for p in ['tools/r1-cost-probe/src/bin/r18_replay.rs','tools/r1-cost-probe/src/bin/r18_replay/readonly_runtime.rs','tools/r1-cost-probe/Cargo.toml','tools/r1-cost-probe/Cargo.lock']:
 put(w/'source'/p,'source/'+p)
log=(w/'runs/harness-check-b/stdout.log').read_text()
line=next(l.strip() for l in log.splitlines() if '--crate-name r18_replay ' in l and l.strip().startswith('Running `'))
cmd=shlex.split(line[len('Running `'):-1]);assert '--emit=dep-info,metadata' in cmd and '-C' in cmd
externs=[]
for i,a in enumerate(cmd):
 if a=='--extern':
  name,path=cmd[i+1].split('=',1);p=Path(path);externs.append({'name':name,'path':path,'bytes':p.stat().st_size,'sha256':sha(p)})
suffix=next(cmd[i+1].removeprefix('extra-filename=') for i,a in enumerate(cmd) if a=='-C' and cmd[i+1].startswith('extra-filename='))
outs=[]
for p in [w/'cargo-target/release/deps'/('r18_replay'+suffix+'.d'),w/'cargo-target/release/deps'/('libr18_replay'+suffix+'.rmeta')]:
 assert p.is_file(),p;outs.append(put(p,'checked-artifacts/'+p.name))
setup=json.loads((w/'setup.json').read_text());oldbin=next(v for k,v in setup['cache_binary_and_depinfo'].items() if k.endswith('/r18_replay'))
current=w/'cargo-target/release/r18_replay';assert sha(current)==oldbin['sha256']
runtime={}
for p in [Path('/home/dombarker/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),Path('/home/dombarker/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo'),Path('/home/dombarker/.cargo/bin/rustup')]:runtime[str(p)]={'sha256':sha(p),'bytes':p.stat().st_size}
post={'source_revision':x['source_revision'],'inputs_sha256':sha(w/'inputs.json'),'all518_source_inputs_rehashed':len(x['files'])==518,'rustc_command':cmd,'actual_extern_artifacts':externs,'checked_outputs':outs,'rust_runtime':runtime,'cache_binary':{'path':str(current),'sha256':sha(current),'unchanged_from_cache':True,'not_candidate_or_executed':True},'only_metadata_typecheck':True,'SBF_or_runtime_execution':False}
(o/'postflight.json').write_text(json.dumps(post,indent=2)+'\n')
with tarfile.open(w/'runtime-harness-evidence.tar.gz','w:gz') as t:
 for p in sorted(o.rglob('*')):
  if p.is_file():t.add(p,arcname=str(p.relative_to(o)),recursive=False)
print(json.dumps({'members':sum(p.is_file() for p in o.rglob('*')),'actual_extern_pins':len(externs),'archive_sha256':sha(w/'runtime-harness-evidence.tar.gz')}))
