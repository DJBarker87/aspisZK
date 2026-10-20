from pathlib import Path
import re,json,hashlib,subprocess
p=Path(__file__).resolve().parent;j=json.loads((p/'extraction/input/source-pins.json').read_text());h=lambda b:hashlib.sha256(b).hexdigest()
assert j['opaque_paths']==[]
for n,pin in j['kit_files'].items():assert h((p/'extraction/input'/n).read_bytes())==pin
for c in j['cuts']:
 b=subprocess.check_output(['git','show',j['revision']+':'+c['path']]);assert b==(p/'extraction/input'/c['destination']).read_bytes();assert h(b)==c['sha256'];assert c['start_byte']==0 and c['end_byte_exclusive']==len(b)
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
for n in ['Types','Funs']:assert clean((p/'extraction/generated/AspisR1CurrentWide'/(n+'.lean')).read_text())==(p/'sources/AspisR1CurrentWide'/(n+'.lean')).read_text()
assert 'axiom ' not in (p/'sources/AspisR1CurrentWide/Funs.lean').read_text()
print('exact frozen full field sources, no opaque paths and only resource-option removal from generated Lean: PASS')
