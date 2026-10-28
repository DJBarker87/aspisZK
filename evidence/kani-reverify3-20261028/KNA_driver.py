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

def controls():
 targets=[('006','KMY_expand_copy_window','assert_eq!(dst[j],',''),('018','KMY_local_window32','assert_eq!(dst[j],',''),('011','KMY_wide_one_window','assert_eq!(dst[j],',''),('012','KMY_limb_window','assert_eq!(dst[j],',''),('017','KMY_scalar_one_window','assert_eq!(dst[j],','')]
 targets += [(str(40+i).zfill(3),'KMY_wide_stage'+str(i),'assert_eq!(out[j],','wide_append_stage') for i in range(6)]
 targets += [('050' if i==0 else '051' if i in [1,10,11,12,13] else str(50+i).zfill(3),'KMY_scalar_stage'+str(i),'assert_eq!(out[j],','scalar_append_stage') for i in range(14)]
 targets += [('074','KMY_capacity_schedules','let expected=[32usize,','KMY_capacity32'),('074','KMY_capacity_schedules','let expected=[16usize,','KMY_capacity16')]
 for idx,(num,h,needle,helper) in enumerate(targets,1):
  a=f'KNA_K{idx+1:03}'
  if idx==8:a='KNA_K029'
  if (E/a/'receipt.json').exists():continue
  parent='KMY_K'+num;cfg=json.loads((OLD/(parent+'.json')).read_text());src=(OLD/'sources'/(archive[parent]['KMY_windows.rs']+'.txt')).read_text()
  start=src.index('fn '+(helper or h)+'(') if helper=='' else src.index('fn '+helper)
  at=src.index(needle,start)
  if 'expected=' in needle:src=src[:at]+src[at:].replace(needle,needle.replace('32usize','33usize').replace('16usize','17usize'),1)
  else:
   # Change only the byte on the left of the selected equality. x == y^1 and x^1 == y are equivalent.
   src=src[:at]+src[at:].replace(needle,needle.replace('[j],','[j] ^ 1u8,'),1)
  src=src.replace('KMY_', 'KNA_').replace('KNA_field.rs','KMY_field.rs')
  cfg['sources']=[x.replace('KMY_windows.rs','KNA_windows.rs').replace('KMY_gate.py','KNA_gate.py') for x in cfg['sources']]
  selected=h.replace('KMY_','KNA_');src=src.replace('fn '+selected+'(', 'fn '+selected+'_selected(');cfg['command']=['python3','KNA_gate.py',a,selected+'_selected'];cfg['parent_gate']=parent;cfg['parent_harness']=h;cfg['negative_control']=True
  # Decoder-only checks and metadata contain no KMX copy gate. Capacity schedules get independent controls for each copy loop.
  result=run(a,cfg,src)
  if result=='PASS':print('FIRST: CONTROL PASSED; DEPENDENT GATE VACUOUS',parent,h,flush=True)
  if result=='ERROR':raise SystemExit('Own input or infrastructure error; inspect '+a)
if __name__=='__main__':controls()
