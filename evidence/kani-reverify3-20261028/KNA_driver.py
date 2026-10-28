"""Task inputs and receipts using the unchanged KMY transport and S2W host runner."""
from pathlib import Path
import types,json,hashlib,subprocess,sys,shlex,time
E=Path(__file__).resolve().parent; OLD=E.parent/'kani-reverify1-20261028'
t=types.ModuleType('transport');t.__file__=str(OLD/'KMY_host.py');exec(compile((OLD/'KMY_host.py').read_text(),t.__file__,'exec'),t.__dict__);t.E=E
PATCH='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67';STUB='c282a1272676cd56fd2702f60b17009bac9d252e495b1508459b01d6ed1cf9d9'
archive=json.loads((OLD/'KMY_SOURCE_ARCHIVE.json').read_text())['attempts']
def run(a,cfg,source):
 assert not (E/a/'receipt.json').exists(),a
 cfg.update(attempt=a,kmx_patch_sha256=PATCH,kmx_stub_file_sha256=STUB,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True)
 assert len(list(E.glob('KNA_K[0-9][0-9][0-9].json')))<90 or cfg['kind']!='kani'
 retry=t.admit(a)
 cfg['reservation_retries']=retry
 files={a+'.json':json.dumps(cfg),'KNA_windows.rs':source,'KNA_gate.py':(E/'KNA_gate.py').read_text()}
 if cfg['kind']=='rust':files.update({n:(E/n).read_text() for n in ['KNA_native.rs','KNA_native_gate.py']})
 r=t.remote_py('from pathlib import Path\nb=Path('+repr(t.B)+')\n'+ '\n'.join('(b/'+repr(n)+').write_text('+repr(s)+')' for n,s in files.items()))
 assert r.returncode==0,r.stderr
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n');(E/'sources').mkdir(exist_ok=True)
 sha=hashlib.sha256(source.encode()).hexdigest();(E/'sources'/f'{sha}.rs').write_text(source)
 r=t.ssh('cd '+shlex.quote(t.B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 if r.returncode==255:
  for retry in range(10):
   time.sleep(60);r=t.remote_py('from pathlib import Path;print(Path('+repr(t.B+'/'+a+'/receipt.json')+').exists())')
   if r.returncode==0 and r.stdout.strip()=='True':break
  else:raise SystemExit('STOP unresolved submitted attempt '+a)
 rc=t.recover(a)
 log=(E/a/'stdout.log').read_text();result='PASS' if cfg['kind']=='rust' and rc['exit_status']==0 else 'TIMEOUT' if 'VERIFICATION:- TIMEOUT' in log or 'timed out' in log.lower() or rc['exit_status']==124 else 'RESOURCE_LIMIT' if rc['exit_status'] in [137,-9] or 'out of memory' in log.lower() or 'sigkill' in log.lower() else 'PASS' if 'VERIFICATION:- SUCCESSFUL' in log else 'COUNTEREXAMPLE' if 'VERIFICATION:- FAILED' in log else 'ERROR'
 (E/a/'classification.json').write_text(json.dumps(dict(result=result,control=cfg.get('negative_control',False),parent=cfg.get('parent_gate'),source_sha256=sha),indent=2)+'\n')
 print(a,result,flush=True)
 return result

