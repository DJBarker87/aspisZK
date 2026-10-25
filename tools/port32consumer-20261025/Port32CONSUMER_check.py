"""--check-equivalent source/data preflight. Never invokes Lean."""
import pathlib,json,hashlib,subprocess,stat,time,resource,sys
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/port32consumer-20261025'
def pin(p):
 p=pathlib.Path(p);h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def state(p):
 s=pathlib.Path(p).lstat();return [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_mode,s.st_uid,s.st_nlink]
def safe(p):
 p=pathlib.Path(p)
 for a in [p,*p.parents]:assert not a.is_symlink(),str(a)
 assert stat.S_ISREG(p.lstat().st_mode) and p.stat().st_uid==501,str(p)
 return p
if __name__=='__main__':
 assert sys.argv[1:]==['--check'];start=time.monotonic()
 assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-port32-consumer-20261025'
 pre=json.loads((E/'Port32CONSUMER_preflight.json').read_text())
 for x in pre['pins']+pre['runtime']:assert pin(safe(x['path']))==x,x['path']
 for x in pre['states']:assert state(safe(x['path']))==x['stat'],x['path']
 src=(T/'Port32CONSUMER_Consumer.lean').read_text()
 assert [l for l in src.splitlines() if l.startswith('import ')]==['import Lean']
 for banned in ['sorry','admit','native_decide','implemented_by','#eval!','doCheck := false','maxHeartbeats','maxRecDepth','region.free','kernel insertion disabled','calls disabled']:
  # getMaxHeartbeats is the required default API, not an option change.
  assert banned not in src.replace('No region.free','No release of regions'),banned
 assert src.count('env.addDeclCore')==2
 assert '#print axioms accepted_original_sdk_s2_s1' in src
 assert 'namespace Port32CONSUMER' in src and 'theorem accepted_original_sdk_s2_s1' in src
 assert 'setEnv checked' in src and 'strict checked-CI/source readback' in src and 'PORT32_COMPLETE' in src
 assert (E/'Port32CONSUMER_CRITERIA.md').exists() and (E/'Port32CONSUMER_DESIGN.md').exists()
 files=[pin(p) for p in sorted(T.iterdir()) if p.is_file()]+[pin(E/n) for n in ['Port32CONSUMER_CRITERIA.md','Port32CONSUMER_DESIGN.md','Port32CONSUMER_preflight.json','Port32CONSUMER_variant-assessment.json','Port32CONSUMER_BEFORE-AFTER.md','Port32CONSUMER_BOUNDARIES.md']]
 # Fresh source/API/notation pins, no command version probe or cache scan.
 base=pathlib.Path(pre['sysroot'])/'src/lean'
 api=[pin(base/p) for p in ['Lean/Environment.lean','Lean/Replay.lean','Lean/Declaration.lean','Lean/Expr.lean','Lean/CoreM.lean','Lean/Util/CollectAxioms.lean','Lean/Util/FoldConsts.lean']]
 notation=[]
 for n in ['Notations','Core']:
  p='docs/research/v8-full-view-zk-20260912/evidence/r367-controlflow-execution/pinned-aeneas/source/Aeneas/Std/Scalar/'+n+'.lean'
  b=subprocess.check_output(['git','show','HEAD:'+p]);notation.append(dict(revision='da9602be04',path=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),assessment='immutable released source/API reconstruction only; object association reused'))
 r=dict(status='PASS TEXT/DATA PREFLIGHT ONLY',command=[sys.executable,'-B',str(pathlib.Path(__file__)),'--check'],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=files,api=api,notation=notation,lean_calls=0,actual_before=355,allocated=[356,357],max_calls=2,forbidden_budgets=0)
 assert r['peak_rss_bytes']<512*1024**2
 (E/'Port32CONSUMER_check.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['status','exit_status','wall_seconds','peak_rss_bytes','lean_calls']}))
