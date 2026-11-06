from pathlib import Path
import hashlib,json,lzma,sys,shutil
b=Path.cwd();a=sys.argv[1];roots=json.loads((b/(a+'.json')).read_text())['env']['LEAN_PATH'].split(':')
modules=[json.loads(l)['module'] for l in (b/'PCC_final_audits/PCC_L068/PCC_LOADED_scan.jsonl').read_text().splitlines()]
pins=[]
for module in modules:
 rel=module.replace('.','/')+'.olean';p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None);assert p is not None,module
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins.append(dict(module=module,path=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
old=json.loads((b/'PCC_PREDECESSOR_PINS.json').read_text())
for p,x in old.items():assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==x['sha256'],p
current=json.loads((b/'PCC_L064-source-review.json').read_text())
for r in current['modules']:
 p=b/'PCC_objects'/(r['module']+'.olean');assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'],r['module']
raw=json.dumps(dict(modules=len(modules),objects=pins,predecessor_pins_checked=len(old),current_support_objects_checked=len(current['modules']),all_pca_and_aeneas_predecessor_pins_unchanged=True),indent=1).encode();d=b/'PCC_closure';d.mkdir(exist_ok=True)
(d/'PCC_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(d/'PCC_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
summary=dict(status='PASS',modules=len(modules),objects=len(pins),predecessor_pins_checked=len(old),support_objects_checked=len(current['modules']),manifest_sha256=hashlib.sha256(raw).hexdigest(),archive_sha256=hashlib.sha256((d/'PCC_CLOSURE_PINS.json.xz').read_bytes()).hexdigest(),host_free_bytes=shutil.disk_usage(b).free)
(b/(a+'-source-pin-summary.json')).write_text(json.dumps(summary,indent=1)+'\n')
print('Resolved closure, Aeneas and unchanged PCA predecessor objects pinned')
