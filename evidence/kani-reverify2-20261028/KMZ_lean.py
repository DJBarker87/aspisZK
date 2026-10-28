"""Single-module focused Lean checks through the existing capped runner."""
from KMZ_driver import *
def compile_one(n,module):
 a=f'KMZ_L{n:03}';p=E/(module+'.lean')
 if (E/a/'receipt.json').exists():return json.loads((E/a/'receipt.json').read_text())['exit_status']
 cfg=json.loads((OLD/'KMY_L010.json').read_text());cfg.update(attempt=a,sources=[p.name],command=[cfg['command'][0],'env','lean','-M7000',p.name,'-o',t.CACHE+'/'+module+'.olean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_time='focused symbolic window composition and axioms audit',kmx_patch_sha256=PATCH,kmx_stub_file_sha256=STUB)
 cfg['deps_fingerprint']['scope']='Mathematical value model only; runtime heap gates are separately required.'
 retry=t.admit(a)
 cfg['reservation_retries']=retry
 if module!='KMZ_Growth':
  names=json.loads((E/'KMZ_LEAN_MANIFEST.json').read_text()) if module=='KMZ_Final' else ['KMZ_Growth']
  r=t.remote_py('import hashlib,json;from pathlib import Path;names='+repr(names)+';print(json.dumps({n:dict(path=str(Path('+repr(t.CACHE)+')/(n+".olean")),sha256=hashlib.sha256((Path('+repr(t.CACHE)+')/(n+".olean")).read_bytes()).hexdigest()) for n in names}))')
  assert r.returncode==0,r.stderr
  cfg['deps_fingerprint']['selected_objects'].update(json.loads(r.stdout))
 r=t.remote_py('from pathlib import Path\nb=Path('+repr(t.B)+')\n(b/'+repr(p.name)+').write_text('+repr(p.read_text())+')\n(b/'+repr(a+'.json')+').write_text('+repr(json.dumps(cfg))+')')
 assert r.returncode==0,r.stderr
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=t.ssh('cd '+shlex.quote(t.B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json',True)
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 if r.returncode==255:
  for retry in range(10):
   time.sleep(60);r=t.remote_py('from pathlib import Path;print(Path('+repr(t.B+'/'+a+'/receipt.json')+').exists())')
   if r.returncode==0 and r.stdout.strip()=='True':break
  else:raise SystemExit('STOP unresolved submitted Lean '+a)
 rc=t.recover(a)
 if rc['exit_status']==0:assert not any('sorryAx' in x for x in rc['print_axioms'])
 return rc['exit_status']
if __name__=='__main__':sys.exit(compile_one(int(sys.argv[1]),sys.argv[2]))
