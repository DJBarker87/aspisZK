from pathlib import Path
import json,lzma,subprocess,hashlib,time
E=Path(__file__).resolve().parent;P=E.parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-pool-retarget-20261105';C='/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104'
selected={}
for f in ['NGJ_CLOSURE_PINS.json.xz','NGJ_POOL_CLOSURE_PINS.json.xz']:
 x=json.loads(lzma.decompress((P/'ledger8-20261105'/f).read_bytes()))
 for r in x['selected_objects']:
  p=r['path'];root=next(z for z in x['LEAN_PATH'] if p.startswith(z+'/'))
  if '/.elan/' in p:continue
  rel=p[len(root)+1:]
  if rel in selected:continue
  if '/NGJ_objects/' in p:p=p.replace('/codex-cx-ledger8-20261105/NGJ_objects/','/codex-cx-ledger8-cache-20261104/NGJ_exports_20261105/')
  selected[rel]=dict(source=p,relative=rel,sha256=r['sha256'],bytes=r['bytes'])
# All retained exports, including the combined import and native fixture support.
for r in json.loads((P/'ledger8-20261105/NGJ_EXPORT.json').read_text())['exports']:
 if '/NGJ_exports_20261105/' in r['path']:
  rel=r['path'].split('/NGJ_exports_20261105/')[1];selected.setdefault(rel,dict(source=r['path'],relative=rel,sha256=r['sha256'],bytes=r['bytes']))
files=list(selected.values());raw=json.dumps(files).encode();(E/'NGK_SEED_INPUTS.json.xz').write_bytes(lzma.compress(raw));(E/'NGK_SEED_INPUTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
code=(P/'ledger8-20261105/NGJ_seed.py').read_text();start=code.index("code='''")+8;end=code.index("'''\nfor retry",start);remote=code[start:end].replace('NGJ_','NGK_').replace('\\\\n','\\n')
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nfiles='+repr(files)+'\n'+remote,text=True,capture_output=True)
 (E/('NGK_SEED_TRANSPORT_'+str(retry)+'.log')).write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr[-1000:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255] or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NGK_CACHE_IMPORTS.json.xz','NGK_CACHE_IMPORTS.json.sha256','NGK_SEED_RESERVATION.json','NGK_SEED_RESERVATION.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
