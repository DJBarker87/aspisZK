from pathlib import Path
import subprocess,sys,json,hashlib,shlex
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90'
roots=['/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025','/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects']
start=int(sys.argv[1]); plan=json.loads((E/'NBN_OPTIONAL_RESULT_PLAN.json').read_text())['missing']
for i,(module,source) in enumerate(plan):
 a=f'NBN_L{start+i:03d}';p=Path(source)
 frozen=subprocess.check_output(['git','show','HEAD:'+source]);assert p.read_bytes()==frozen
 code='from pathlib import Path; import json; print(json.dumps([str(Path(r)/( '+repr(module+'.olean')+')) for r in '+repr(roots)+' if (Path(r)/'+repr(module+'.olean')+').exists()]))'
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(code)],capture_output=True,text=True)
 assert r.returncode==0,r.stderr
 assert json.loads(r.stdout)==[],'object already present; reuse it, never overwrite'
 pin=dict(module=module,source=source,source_sha256=hashlib.sha256(frozen).hexdigest(),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),absence_roots=roots,attempt=a,scope='missing unchanged dependency; ONE build into required persistent cache')
 (E/(a+'-DEPENDENCY.json')).write_text(json.dumps(pin,indent=2)+'\n')
 with (E/(a+'-console.log')).open('w') as f:r=subprocess.run([sys.executable,str(E/'NBN_build.py'),a,source,module],stdout=f,stderr=subprocess.STDOUT)
 q=E/a/'receipt.json';assert r.returncode==0 and q.exists(),'inspect before further build'
 x=json.loads(q.read_text());print(a,module,x['exit_status'],x['wall_seconds'],flush=True)
 assert x['exit_status']==0,'stop dependency chain; never retry unchanged'
 for l in x['print_axioms']:
  assert 'sorryAx' not in l and 'axiom ' not in l
