"""Task inputs through the unchanged KMY admission/transport and S2W runner."""
from pathlib import Path
import types,json,subprocess,shlex,hashlib,time,sys
E=Path(__file__).resolve().parent
p=E.parent/'kani-reverify1-20261028/KMY_host.py'
t=types.ModuleType('transport');t.__file__=str(p);exec(compile(p.read_text(),str(p),'exec'),t.__dict__);t.E=E
B=t.B

def run(a,harness,control=False):
 assert not (E/a/'receipt.json').exists()
 source=(E/'KNF_harness.rs').read_text().replace('const KNF_XOR:u32=0;',f'const KNF_XOR:u32={int(control)};')
 cfg=dict(attempt=a,kind='kani',sources=['KNF_harness.rs','KNF_field.rs','KNF_wide_exact.rs','KNF_gate.py','KMY_src/Cargo.lock'],command=['python3','KNF_gate.py',a,harness],timeout=180,env={'PATH':'/home/dombarker/.kani/kani-0.67.0/bin:/home/dombarker/.cargo/bin:/usr/bin:/bin','CARGO_NET_OFFLINE':'true','RUSTFLAGS':'--edition=2021 -C opt-level=3','CARGO_BUILD_JOBS':'1'},deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','graph_receipt':a+'-graph.json','cache':t.CACHE},expected_time='optimized standalone codegen then named array/decoder CBMC property; no field elimination',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,negative_control=control,selected_harness=harness)
 cfg['reservation_retries']=t.admit(a)
 files={a+'.json':json.dumps(cfg),'KNF_harness.rs':source,**{n:(E/n).read_text() for n in ['KNF_gate.py','KNF_field.rs','KNF_wide_exact.rs']}}
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 (E/'sources').mkdir(exist_ok=True);(E/'sources'/(a+'.rs')).write_text(source)
 # scp avoids the shell's per-argument size limit for frozen field source.
 upload=E/'sources'/'KNF_harness.rs';upload.write_text(source)
 paths=[E/(a+'.json'),upload]+[E/n for n in ['KNF_gate.py','KNF_field.rs','KNF_wide_exact.rs']]
 for retry in range(10):
  r=subprocess.run(['scp','-q','-o','ConnectTimeout=15',*[str(p) for p in paths],t.H+':'+B+'/'],capture_output=True,text=True)
  with (E/'KNF_UPLOAD.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,retry=retry,exit=r.returncode,stderr=r.stderr))+'\n')
  if r.returncode!=255:break
  if retry<9:time.sleep(60)
 assert r.returncode==0,r.stderr
 r=t.ssh('cd '+shlex.quote(B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 if r.returncode==255:
  # A possibly submitted command is never resubmitted.
  for retry in range(10):
   time.sleep(60);q=t.remote_py('from pathlib import Path;print(Path('+repr(B+'/'+a+'/receipt.json')+').exists())')
   if q.returncode==0 and q.stdout.strip()=='True':break
  else:raise SystemExit('STOP unresolved submitted attempt '+a)
 rc=t.recover(a)
 log=(E/a/'stdout.log').read_text()
 result='TIMEOUT' if rc['exit_status']==124 or 'VERIFICATION:- TIMEOUT' in log else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'COUNTEREXAMPLE' if 'VERIFICATION:- FAILED' in log else 'ERROR'
 (E/a/'classification.json').write_text(json.dumps(dict(result=result,control=control,harness=harness),indent=2)+'\n')
 print(a,result,flush=True)
 return result
if __name__=='__main__':run(sys.argv[1],sys.argv[2],len(sys.argv)>3)
