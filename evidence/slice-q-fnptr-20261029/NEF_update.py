from NEF_host import *
import sys,hashlib,difflib
label,relative,local=sys.argv[1:]
admit(label)
t=(E/local).read_text()
r=py(f'from pathlib import Path;import hashlib; p=Path({(B+"/NEF_src/"+relative)!r});p.write_text({t!r});print(hashlib.sha256(p.read_bytes()).hexdigest())');assert r.returncode==0,r.stderr
pins=json.loads((E/'NEF_SCRATCH_PINS.json').read_text());pins[relative]=r.stdout.strip();(E/'NEF_SCRATCH_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(E/(label+'-update.json')).write_text(json.dumps(dict(path=relative,input=local,sha256=hashlib.sha256(t.encode()).hexdigest()))+'\n')
