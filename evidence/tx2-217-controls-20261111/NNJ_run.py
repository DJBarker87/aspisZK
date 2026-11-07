"""Own serial controls client, using unchanged reservation and S2W host runner."""
from NNJ_transport import *
import shlex,sys,base64
sha=lambda b:hashlib.sha256(b).hexdigest()
def run(a,h,expected,env_extra=None,control=''):
 assert not (E/a).exists()
 done=[json.loads(l) for l in (E/'NNJ_ATTEMPTS.jsonl').read_text().splitlines()]
 assert sum(x.get('kind')=='kani' for x in done)<16
 admission(a)
 env={'PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin','TMPDIR':B+'/NNJ_tmp','CARGO_TARGET_DIR':B+'/NNJ_target','CARGO_HOME':B+'/NNJ_cargo','CARGO_NET_OFFLINE':'true','CARGO_BUILD_JOBS':'1','RAYON_NUM_THREADS':'1'}
 env.update(env_extra or {})
 files={'NNJ_gate.py':(E/'NNJ_gate.py').read_text()}
 cfg=dict(attempt=a,kind='kani',module=h,command=['python3','NNJ_gate.py',a,h],env=env,sources=list(files)+['NNJ_SEED.json','NNJ_HARNESSES.patch','NNJ_DEPENDENCY.patch'],timeout=180,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,deps_fingerprint={'note':'full Rust source and private dependency manifests checked inside gate; no Lean invoked'},expected_time='optimized Kani compilation then one named calibration '+h)
 files[a+'.json']=json.dumps(cfg,indent=1)+'\n'
 r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():(b/n).write_text(t)
''');assert r.returncode==0,r.stderr
 r=ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',submitted=True)
 raw=(r.stdout+r.stderr).encode();(E/(a+'-launcher.log.xz')).write_bytes(lzma.compress(raw));(E/(a+'-launcher.log.sha256')).write_text(sha(raw)+'\n')
 r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});a={a!r};names=[p for p in (b/a).rglob('*') if p.is_file()]+[b/(a+'.json')]+[p for pat in ['-graph*','-source*','-lock*','-metadata*'] for p in b.glob(a+pat)]
print(json.dumps({{str(p.relative_to(b)):base64.b64encode(p.read_bytes()).decode() for p in names}}))
''');assert r.returncode==0,r.stderr
 out=json.loads(r.stdout)
 for n,t in out.items():
  p=E/n;p.parent.mkdir(parents=True,exist_ok=True);raw=base64.b64decode(t)
  if n.endswith('.log'):
   p.with_name(p.name+'.xz').write_bytes(lzma.compress(raw));p.with_name(p.name+'.sha256').write_text(sha(raw)+'\n')
  else:p.write_bytes(raw)
 rc=json.loads((E/a/'receipt.json').read_text());log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 actual='PASS' if 'VERIFICATION:- SUCCESSFUL' in log and rc['exit_status']==0 else 'FAIL' if 'VERIFICATION:- FAILED' in log and 'Failed Checks:' in log else 'NONSEMANTIC_FAILURE'
 summary={k:rc[k] for k in ['attempt','kind','module','source_revision','source_hashes','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}
 summary.update(actual_verdict=actual,expected_verdict=expected,control=control,full_receipt=a+'/receipt.json')
 with (E/'NNJ_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(summary)+'\n')
 controls=json.loads((E/'NNJ_CONTROLS.json').read_text());controls.append(dict(shape='Result<Box<Lane>,ProgramError>' if 'fidelity' in h else 'Result<(),ProgramError> with &mut [M31;8]',control=control,attempt=a,expected_verdict=expected,actual_verdict=actual,harness=h,receipt=a+'/receipt.json'));(E/'NNJ_CONTROLS.json').write_text(json.dumps(controls,indent=1)+'\n')
 print(json.dumps(summary),flush=True)
 if actual!=expected:
  print(log[-6500:],flush=True);return False
 return True
if __name__=='__main__':
 a,h,expected,control=sys.argv[1:5];env=json.loads(sys.argv[5]) if len(sys.argv)>5 else {}
 sys.exit(0 if run(a,h,expected,env,control) else 1)
