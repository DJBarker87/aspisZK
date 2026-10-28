from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent
c=json.loads((B/'JHw_preflight.json').read_text()); paths=list(map(Path,c['env']['LEAN_PATH'].split(':')))
expected=json.loads((B/'JHw_EXPECTED_PINS.json').read_text())
byname={}
for p,hs in expected.items():byname.setdefault(Path(p).name,set()).update(hs)
fallback=json.loads((B/'JHw_SOURCE_IMPORTS.json').read_text())
seen=set();rows=[];missing=[];unverified=[];source_missing=[]
prefixes=('JHv_','JHu_','JHq_','JHn_','NCX_','NCV_')
def visit(m):
 if m in seen:return
 seen.add(m);key=m.replace('.','/')
 p=next((r/(key+'.olean') for r in paths if (r/(key+'.olean')).is_file()),None)
 if p is None:missing.append(m);return
 if m.startswith(prefixes):
  for q in [p,Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')]:
   if not q.exists():continue
   h=hashlib.sha256(q.read_bytes()).hexdigest();known=expected.get(str(q),{})
   ok=h in known or h in byname.get(q.name,set())
   rows.append(dict(module=m,path=str(q),sha256=h,bytes=q.stat().st_size,historical_match=ok))
   if not ok:unverified.append(str(q))
 s=next((r/(key+'.lean') for r in paths if (r/(key+'.lean')).is_file()),None)
 if s is None:
  if m in fallback:
   for n in fallback[m]['imports']:visit(n)
  elif m.startswith(prefixes):source_missing.append(m)
  return
 for l in s.read_text().splitlines():
  if l.startswith('import '):
   for n in l[7:].split():visit(n)
for root in ['JHv_Validation','JHi_TX2','JHq_TX1','JHn_Joint','JHi_SHAProof','JHi_SHAPublic','JHi_SHAChecksum']:visit(root)
out=dict(roots=['JHv_Validation','JHi_TX2','JHq_TX1','JHn_Joint','JHi_SHAProof','JHi_SHAPublic','JHi_SHAChecksum'],visited=len(seen),objects=rows,missing_objects=missing,unverified=unverified,targeted_sources_missing=source_missing)
(B/'JHw_CLOSURE_PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:(len(v) if isinstance(v,list) else v) for k,v in out.items()}))
print('unverified',unverified,'missing',missing,'targeted sources missing',source_missing)
raise SystemExit(bool(missing or unverified or source_missing))
