from KNE_driver import *
import re
EXTRA='/home/dombarker/project-offloads/codex-cx-assoc-a6-cache-20261027/XSc_objects:/home/dombarker/project-offloads/codex-cx-assoc-a6-cache-20261027/XRx_objects:/home/dombarker/project-offloads/codex-cx-assoc-a2-cache-20261027/XRw_objects:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025:/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'
def compile_one(module):
 n=len(list(E.glob('KNE_L[0-9][0-9][0-9].json')))+1;assert n<=50
 a=f'KNE_L{n:03}';p=E/(module+'.lean')
 cfg=json.loads((E.parent/'kani-reverify4-20261028/KND_L001.json').read_text())
 cfg.update(attempt=a,sources=[p.name],command=[cfg['command'][0],'env','lean','-j1','-M7000','-DElab.async=false',p.name,'-o',t.CACHE+'/'+module+'.olean'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,expected_time='single focused model schedule/composition lemma; symbolic byte lengths')
 cfg['env']['LEAN_PATH']+=':'+EXTRA
 cfg['deps_fingerprint']['scope']='Adopted LPm coherent objects and KND schedule; conditional native heap association retained.'
 retry=t.admit(a);cfg['reservation_retries']=retry
 names=re.findall(r'^import (\w+)',p.read_text(),re.M);paths=cfg['env']['LEAN_PATH'].split(':')
 r=t.remote_py('import hashlib,json;from pathlib import Path;names='+repr(names)+';paths='+repr(paths)+';selected={}\nfor n in names:\n p=next(Path(d)/(n+".olean") for d in paths if (Path(d)/(n+".olean")).is_file());selected[n]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())\nprint(json.dumps(selected))')
 assert r.returncode==0,r.stderr
 cfg['deps_fingerprint']['selected_objects']=json.loads(r.stdout)
 r=t.remote_py('from pathlib import Path\nb=Path('+repr(t.B)+')\n(b/'+repr(p.name)+').write_text('+repr(p.read_text())+')\n(b/'+repr(a+'.json')+').write_text('+repr(json.dumps(cfg))+')')
 assert r.returncode==0,r.stderr
 (E/(a+'.json')).write_text(json.dumps(cfg,indent=2)+'\n')
 r=submit(a,'cd '+shlex.quote(t.B)+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+a+'.json')
 (E/(a+'-launcher.log')).write_text(r.stdout+r.stderr)
 if r.returncode==255:
  for retry in range(10):
   time.sleep(60);r=t.remote_py('from pathlib import Path;print(Path('+repr(t.B+'/'+a+'/receipt.json')+').exists())')
   if r.returncode==0 and r.stdout.strip()=='True':break
  else:raise SystemExit('STOP unresolved submitted Lean '+a)
 rc=t.recover(a)
 if rc['exit_status']==0:assert not any('sorryAx' in x for x in rc['print_axioms'])
 print((E/a/'stdout.log').read_text(),flush=True)
 return rc['exit_status']
if __name__=='__main__':sys.exit(compile_one(sys.argv[1]))
