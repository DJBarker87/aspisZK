from pathlib import Path
import subprocess,hashlib,json,re
r=Path(__file__).resolve().parent;repo=r
while not (repo/'.git').exists():repo=repo.parent
b=r/'extraction';pins=json.loads((b/'input/source-pins.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest()
for name,pin in pins['kit_files'].items():assert h((b/'input'/name).read_bytes())==pin
for name,pin in pins['source_files'].items():assert h(subprocess.check_output(['git','show',pins['revision']+':'+name],cwd=repo))==pin
for cut in pins['cuts']:
 raw=subprocess.check_output(['git','show',pins['revision']+':'+cut['path']],cwd=repo)
 selected=raw[cut['start_byte']:cut['end_byte_exclusive']]
 assert h(selected)==cut['sha256'] and selected==(b/'input/fragments'/(cut['name']+'.rs')).read_bytes()
for n in ['Types','Funs']:
 raw=(b/'generated/AspisR1EbyKFinish'/(n+'.lean')).read_text()
 clean=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth) .*\n','',raw,flags=re.M)
 if n=='Funs':clean=clean.replace('import AspisR1EbyKFinish.FunsExternal','import SelectorArrayMapRuntimeSlice')
 assert clean==(r/'sources/AspisR1EbyKFinish'/(n+'.lean')).read_text()
print('Exact frozen canonical reducer/Dot finish cuts and complete generated adapter: PASS')
