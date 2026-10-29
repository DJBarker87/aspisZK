"""Optimized deployed-configuration finite checks; no proof or extraction claim."""
from pathlib import Path
import subprocess,json,hashlib,sys
P=Path('/home/dombarker/project-offloads/codex-pv-rj4idb-20261029');cfg=json.loads((P/'native-plan.json').read_text());sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();suite=sys.argv[1]
for f in cfg['unit_records']:
 assert sha(Path(f['path']))==f['sha256'],f['path']
for f in cfg['source_records']:
 assert sha(Path(f['path']))==f['sha256'],f['path']
R=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028/client-target/release/deps')
rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc'
libs=['aspis_core'] if suite=='powers' else ['aspis_statement','aspis_core']
cmd=[rustc,'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','-L','dependency='+str(R)]
rlibs=[]
for name in libs:
 fs=list(R.glob('lib'+name+'-*.rlib'));assert len(fs)==1,(name,fs)
 cmd+=['--extern',name+'='+str(fs[0])];rlibs.append(dict(path=str(fs[0]),sha256=sha(fs[0])))
cmd += [str(P/(suite+'.rs')),'-o',str(P/('native-'+suite))]
print('phase: optimized rustc compilation, then '+suite+' finite validation; no dense elimination',flush=True)
r=subprocess.run(cmd,capture_output=True,text=True)
(P/'evidence'/('native-'+suite+'-compile.log')).write_text(r.stdout+r.stderr)
if r.returncode: print(r.stdout+r.stderr);sys.exit(r.returncode)
x=subprocess.run([str(P/('native-'+suite))],capture_output=True,text=True)
rec=dict(evidence_class='finite validation, deployed-configuration harness',toolchain=subprocess.check_output([rustc,'-vV'],text=True),command=cmd,source_sha256=sha(P/(suite+'.rs')),powers_source_sha256=sha(P/'powers-source.rs'),rlibs=rlibs,binary_sha256=sha(P/('native-'+suite)),exit=x.returncode,stdout=x.stdout,stderr=x.stderr,source_revision=cfg['source_revision'],configuration=cfg['configuration'],native_configuration_input_pins=cfg['source_records'])
(P/'evidence'/('native-'+suite+'-result.json')).write_text(json.dumps(rec,indent=2)+'\n');print(x.stdout+x.stderr,flush=True);sys.exit(x.returncode)
