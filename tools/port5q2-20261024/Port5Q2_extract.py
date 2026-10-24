#!/usr/bin/env python3
from pathlib import Path
import json,subprocess,shlex,hashlib,sys
R=Path(__file__).resolve().parents[2];T=R/'tools/port5q2-20261024';E=R/'evidence/port5q2-20261024'
H='dombarker@100.108.41.90'; B='/home/dombarker/project-offloads/codex-cx-port5q2-20261024';OLD='/home/dombarker/project-offloads/codex-cx-ports3-20261023'
kind=sys.argv[1]; n=1+len(list(T.glob(kind+'-*.json')));a=f'{kind}-{n:03d}'
pins=json.loads((R/'evidence/ports3-20261023/kani-001/receipt.json').read_text())['deps_fingerprint']['source_snapshot_pins']
assert all(hashlib.sha256((R/k).read_bytes()).hexdigest()==v for k,v in pins.items())
if kind=='charon':
 subprocess.run(['ssh',H,f'mkdir -p {B}/src && rsync -a --exclude target {OLD}/src/ {B}/src/'],check=True)
 c=json.loads((R/'tools/ports3-20261023/charon-004.json').read_text());cmd=c['command'];i=cmd.index('--include');j=cmd.index('--consts');kept=[]
 for x in range(i,j,2):
  if cmd[x]=='--include' and not any(s in cmd[x+1] for s in ['candidate::','}::','::checkpoint','::finish_relation','::accumulate_batched_with_node']):kept+=cmd[x:x+2]
 roots=['crate::verifier::_::'+f for f in ['raw','k','e']]
 roots+=['crate::verifier::'+f for f in ['validate_checkpoint_queries','read_checkpoint_semantic_alpha','read_checkpoint_weights']]
 cmd=cmd[:i]+sum((['--include',root] for root in roots),[])+sum((['--start-from',root] for root in roots if '{' not in root),[])+kept+cmd[j:]
 cmd=[s.replace(OLD,B).replace('Port3_StageChildren','Port5Q2_ReaderHelpers') for s in cmd]
 c.update(command=cmd,timeout=240,expected_time='Optimized Rust compilation and MIR extraction of six small reader helpers, no arithmetic elimination or whole-reader replay')
 c['env']['CARGO_TARGET_DIR']=B+'/charon-target'
else:
 c=json.loads((R/'tools/ports3-20261023/aeneas-004.json').read_text());c['command']=[s.replace(OLD,B).replace('Port3_StageChildren','Port5Q2_ReaderHelpers') for s in c['command']];c['sources']=['Port5Q2_ReaderHelpers.llbc'];c['expected_time']='Aeneas translation of isolated current reader helpers, no proof replay'
c.update(attempt=a,kind=kind,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),deps_fingerprint={'source_snapshot_pins':pins})
check='from pathlib import Path;import hashlib;r=Path('+repr(B+'/src')+');p='+repr(pins)+';assert all(hashlib.sha256((r/k).read_bytes()).hexdigest()==v for k,v in p.items())'
subprocess.run(['ssh',H,'python3 -c '+shlex.quote(check)],check=True)
p=T/f'{a}.json';p.write_text(json.dumps(c,indent=2)+'\n')
admission=(T/'Port5Q2_compile.py').read_text().split("admission='''",1)[1].split("'''",1)[0]
r=subprocess.run(['ssh',H,'python3 -c '+shlex.quote(admission)],capture_output=True,text=True,check=True);(E/f'{a}-reservation.json').write_text(r.stdout)
subprocess.run(['scp','-q',str(p),str(T/'Port5Q2_run_host.py'),H+':'+B+'/'],check=True)
r=subprocess.run(['ssh',H,f'cd {B} && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 Port5Q2_run_host.py {a}.json'],capture_output=True,text=True)
(E/f'{a}-launcher.log').write_text(r.stdout+r.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+a,str(E)],check=True)
if kind=='aeneas':subprocess.run(['scp','-qr',H+':'+B+'/generated-complete/Port5Q2_ReaderHelpers/.',str(E/'reader-helpers')],check=True)
print(r.stdout);print(r.stderr);sys.exit(r.returncode)
