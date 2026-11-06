from pathlib import Path
import json,lzma,hashlib,os,sys
B=Path.cwd();src=Path('/home/dombarker/project-offloads/codex-cx-ledger15-20261108/NJO_CLOSURE_PINS.json.xz')
expected=json.loads((B/'NJQ_CACHE_INPUTS.json').read_text());raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()==expected['sha256']
x=json.loads(lzma.decompress(raw));paths=os.environ['LEAN_PATH'].split(':');wrong=[];missing=[];seen=[]
for row in x['selected_objects']:
 suffix=next(v for v in ['.olean.private','.olean.server','.olean','.ir'] if row['path'].endswith(v))
 rel=row['module'].replace('.','/')+suffix
 p=next((Path(root)/rel for root in paths if (Path(root)/rel).is_file()),None)
 if p is None:missing.append(rel);continue
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if h!=row['sha256']:wrong.append(dict(module=row['module'],suffix=suffix,expected=row['sha256'],selected=h,path=str(p)))
 seen.append(dict(module=row['module'],suffix=suffix,path=str(p),sha256=h))
result=dict(status='PASS' if not wrong and not missing else 'FINDING',baseline_files=len(x['selected_objects']),selected=len(seen),missing=missing,mismatches=wrong,paths=paths)
(B/'NJQ_CACHE_PREFLIGHT.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['paths','mismatches','missing']}|dict(missing=len(missing),mismatches=len(wrong))))
sys.exit(bool(wrong or missing))
