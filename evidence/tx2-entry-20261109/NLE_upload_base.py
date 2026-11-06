from NLE_transport import *
import base64,sys
name=sys.argv[1];admission(name)
files={n:base64.b64encode((E/n).read_bytes()).decode() for n in ['NLE_BASE.json.xz','NLE_BASE.json.sha256','NLE_stage_base.py']}
r=ssh('python3',f'''from pathlib import Path
import json,base64,subprocess
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():(b/n).write_bytes(base64.b64decode(t))
r=subprocess.run(['python3',str(b/'NLE_stage_base.py')],capture_output=True,text=True)
print(r.stdout);print(r.stderr);print('exit',r.returncode)
''')
(E/(name+'-stage.log')).write_text(r.stdout+r.stderr)
assert r.returncode==0 and 'exit 0' in r.stdout,r.stdout+r.stderr
print(name+' base staged')
