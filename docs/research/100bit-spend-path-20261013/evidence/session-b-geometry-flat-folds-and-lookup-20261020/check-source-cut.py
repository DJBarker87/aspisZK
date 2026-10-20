from pathlib import Path
import json,hashlib,re,subprocess
root=Path(__file__).resolve().parent
h=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
b=root/'source-cut';pins=json.loads((b/'input/source-pins.json').read_text())
for f,v in pins['kit_files'].items():assert h(b/'input'/f)==v,f
repo=root
while not (repo/'.git').exists():repo=repo.parent
for cut in pins['cuts']:
 raw=subprocess.check_output(['git','show',pins['revision']+':'+cut['path']],cwd=repo)
 expected=raw[cut['start_byte']:cut['end_byte_exclusive']]
 assert hashlib.sha256(expected).hexdigest()==cut['sha256']
 assert expected==(b/'input/fragments'/(cut['name']+'.rs')).read_bytes()
for name in ['Types','Funs']:
 raw=(b/'generated/AspisR1GeometryLookup'/(name+'.lean')).read_text()
 cleaned=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) .*\n','',raw,flags=re.M)
 assert cleaned==(root/'sources/AspisR1GeometryLookup'/(name+'.lean')).read_text()
assert not list((b/'generated').rglob('*External*'))
print('Exact frozen record/method cut and resource-line-only Lean adapter: PASS')
