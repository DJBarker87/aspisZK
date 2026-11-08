from pathlib import Path
import json,lzma,hashlib,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-fin-host-20261108')
P=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NNM_20261111')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((P/'NNM_EXPORT.json').read_text());pins=json.loads(lzma.open(P/'NNM_CLOSURE_PINS.json.xz').read());B.mkdir(exist_ok=True)
assert shutil.disk_usage(B).free>=40_000_000_000
out=B/'NNO_exports';out.mkdir(exist_ok=True)
records=[]
for p in Path(x['export']).iterdir():
 if p.is_file():
  q=out/p.name
  if not q.exists():shutil.copy2(p,q)
  assert sha(q)==sha(p)
  records.append(dict(source=str(p),copy=str(q),sha256=sha(q),bytes=q.stat().st_size))
paths=[str(out)]+x['LEAN_PATH'][1:]
selected=[];errors=[]
for z in pins['selected_objects']:
 if not z['path'].endswith('.olean'):continue
 rel=z['module'].replace('.','/')+'.olean'
 p=next((Path(r)/rel for r in paths if(Path(r)/rel).is_file()),None)
 if p is None or sha(p)!=z['sha256']:errors.append(dict(expected=z,actual=str(p),hash=sha(p)if p else None))
 selected.append(dict(module=z['module'],path=str(p),sha256=sha(p)if p else None))
rsl=[z for z in selected if z['module'].startswith('RSL_')]
assert not errors,errors[:3]
assert next(z for z in rsl if z['module']=='RSL_Base')['sha256']=='5514b5480d9b76d40f9911c6c4772ff256827339577560bc1559ca57dc28ee81'
mods=['NMV_NoWriteSdk','NMV_WeakFold','NMV_PhysicalCarrier','NMV_Stage1Frame','NNC_G1a','NMW_Branches']
extra=[]
for m in mods:
 p=next((Path(r)/(m+'.olean') for r in paths if(Path(r)/(m+'.olean')).is_file()),None)
 extra.append(dict(module=m,path=str(p)if p else None,sha256=sha(p)if p else None,in_ledger29_pins=any(z['module']==m for z in selected)))
(B/'NNO_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
(B/'NNO_COHERENCE.json').write_text(json.dumps(dict(status='PASS',base_export=x['export'],copied_files=records,selected_objects=selected,rsl=rsl,extras=extra,closure_pins_sha256=sha(P/'NNM_CLOSURE_PINS.json.xz'),conclusion='Both child roots resolve through the ledger29 rev4 RSL selection; original dd8125eb closure is superseded. No NMX rebuild.',errors=errors),indent=1)+'\n')
print(json.dumps(dict(status='PASS',selected_modules=len(selected),copied_files=len(records),extras=extra)))
