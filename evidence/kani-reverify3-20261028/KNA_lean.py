"""Single-module focused checks via the existing capped runner."""
from KNA_driver import *
import re

def compile_one(module):
 previous=list(E.glob('KNA_L[0-9][0-9][0-9].json'));n=len(previous)+1
 assert n<=40
 a=f'KNA_L{n:03}';p=E/(module+'.lean')
 assert not (E/a/'receipt.json').exists()
 cfg=json.loads((OLD/'KMY_L010.json').read_text())
 cfg.update(attempt=a,sources=[p.name],command=[cfg['command'][0],'env','lean','-M7000',p.name,'-o',t.CACHE+'/'+module+'.olean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='focused symbolic frame/window composition and axioms audit',kmx_patch_sha256=PATCH,kmx_stub_file_sha256=STUB)
 cfg['deps_fingerprint']['scope']='Mathematical value model; missing runtime heap gates earn no credit.'
 retry=t.admit(a);cfg['reservation_retries']=retry
 names=re.findall(r'^import (\w+)',p.read_text(),re.M)
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
if __name__=='__main__':
 modules=json.loads((E/'KNA_LEAN_MANIFEST.json').read_text())
 for module in modules:
  receipts=[json.loads(p.read_text()) for p in E.glob('KNA_L*/receipt.json')]
  if any(r['sources']==[module+'.lean'] and r['exit_status']==0 for r in receipts):continue
  if compile_one(module)!=0:raise SystemExit('Inspect focused proof '+module)
