"""Retain own objects; pin first-resolved partial and isolated-forest closures."""
from pathlib import Path
import json,subprocess,time
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-owner-dedupe-20261107';C='/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat'
# Isolated NHJ imports need pins too; graph is an independent source baseline.
g={r['module']:r['imports']for r in map(json.loads,(E/'NIM_EXPECTED_IMPORTS.jsonl').read_text().splitlines())};todo=['NIM_COMBINED_IMPORT'];extra=set()
while todo:
 m=todo.pop()
 if m in extra:continue
 extra.add(m);todo+=g.get(m,[])
code='''from pathlib import Path
import json,hashlib,lzma,shutil,subprocess,sys
b=Path(B);c=Path(C);export=c/'NIM_exports_20261107'
with (b/'NIM_EXPORT_barrier.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIM_EXPORT_admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((b/'NIM_EXPORT_admission.json').read_text())
if r.returncode!=0 or ad.get('allowed')is not True:print(json.dumps(ad));sys.exit(78)
export.mkdir(exist_ok=True);copied=[]
for p in (b/'NIM_objects').rglob('*'):
 if p.is_file():
  q=export/p.relative_to(b/'NIM_objects');q.parent.mkdir(parents=True,exist_ok=True);h=hashlib.sha256(p.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(p,q)
  copied.append(dict(source=str(p),path=str(q),sha256=h,bytes=q.stat().st_size))
x=json.loads((b/'NIM_L033.json').read_text());roots=x['env']['LEAN_PATH'].split(':');loaded={json.loads(l)['module']for l in(b/'NIM_LOADED_scan.jsonl').read_text().splitlines()};modules=loaded|set(extra);pins=[]
for module in sorted(modules):
 rel=module.replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if(Path(root)/rel).is_file()),None);assert p is not None,module
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=module,path=str(z),sha256=hashlib.sha256(z.read_bytes()).hexdigest(),bytes=z.stat().st_size,provenance='full combined forest loaded scanner'))
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=pins,modules=len(modules),partial_scanned_modules=len(loaded),isolated_NHJ_expected_closure=len(extra),full_composition_pass=True)).encode();(b/'NIM_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(b/'NIM_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
(b/'NIM_EXPORT.json').write_text(json.dumps(dict(export=str(export),files=copied,bytes=sum(p['bytes']for p in copied),admission=ad,exit=r.returncode,cache_retained=str(c),binaries_exported=False,full_import_object_exists=(b/'NIM_objects/NIM_COMBINED_IMPORT.olean').exists(),disk_free=shutil.disk_usage(b).free),indent=1));print(json.dumps(dict(exports=len(copied),closure_objects=len(pins),aeneas_objects=sum('/Aeneas/'in p['path']or'/AeneasMeta/'in p['path']for p in pins))))
'''
for retry in range(11):
 r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15',H,'python3'],input='B='+repr(B)+'\nC='+repr(C)+'\nextra='+repr(sorted(extra))+'\n'+code,capture_output=True,text=True)
 (E/f'NIM_EXPORT_TRANSPORT_{retry}.log').write_text(r.stdout+r.stderr);print(r.stdout[-1200:],r.stderr[-1200:],flush=True)
 if r.returncode==0:break
 if r.returncode not in [78,255]or retry==10:raise SystemExit(r.returncode)
 time.sleep(60 if r.returncode==255 else 180)
for n in ['NIM_EXPORT.json','NIM_CLOSURE_PINS.json.xz','NIM_CLOSURE_PINS.json.sha256','NIM_EXPORT_admission.json','NIM_EXPORT_barrier.log']:
 r=subprocess.run(['ssh','-o','ControlMaster=no',H,'cat '+B+'/'+n],capture_output=True);assert r.returncode==0;(E/n).write_bytes(r.stdout)
