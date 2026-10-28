"""Terminal read-only cache inventory and cleanup of only own build scratch."""
from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent
assert (E/'NBR_BUDGET_STOP.json').exists() and not (E/'NBR_ACTIVE.json').exists()
code='''from pathlib import Path
import json,subprocess,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-native-prepare3-20261028')
c=Path('/home/dombarker/project-offloads/codex-cx-prepare-cache-20261028')
live=[l for l in subprocess.check_output(['ps','-eo','pid,args'],text=True).splitlines() if str(b/'NBR_target') in l or 'S2W_lean_host.py NBR_' in l or 'S2W_run_host.py NBR_' in l]
assert not live,live
objects={str(p.relative_to(c)):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sorted(c.rglob('*')) if p.is_file()}
deleted=[]
for n in ['NBR_target','NBR_tmp']:
 p=b/n
 if p.exists():shutil.rmtree(p);deleted.append(str(p))
print(json.dumps(dict(cache=str(c),end=objects,deleted=deleted,live=live,cache_retained=c.exists(),source_overlay_retained=(b/'NBR_src').exists(),resolved_library=json.loads((b/'NBR_LIBRARY_RESOLVED.json').read_text())),indent=2))
'''
for n in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
 (E/('NBR_FINISH_HOST-'+str(n)+'.log')).write_text(r.stdout+r.stderr)
 if r.returncode!=255:break
 if n<10:print('transport retry60s',flush=True);time.sleep(60)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout);start=json.loads((E/'NBR_CACHE_START.json').read_text())
assert all(out['end'].get(k)==v for k,v in start['imported'].items()),'seed object changed'
assert out['resolved_library']==json.loads((E/'NBR_LIBRARY_RESOLVED_INHERITED.json').read_text()),'library pin drift'
out['seed_imported_unchanged']=True
(E/'NBR_CACHE_END.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(cache_objects=len(out['end']),imported_unchanged=True,resolved_library_files=len(out['resolved_library']),deleted=out['deleted'])))
