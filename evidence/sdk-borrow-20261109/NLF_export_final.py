from NLF_formal import *
import base64
mods=sorted(p.stem for p in E.glob('NLF_*.lean') if p.stem not in ['NLF_ProofDriver','NLF_ScanDriver'])
files={'NLF_export_host.py':(E/'NLF_export_host.py').read_text(),'NLF_EXPORT_MODULES.json':json.dumps(mods)}
r=run('NLF_L081','inspect','export-and-selected-closure-pins',['python3','NLF_export_host.py'],files)
assert r['exit_status']==0
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});names=['NLF_EXPORT.json','NLF_CLOSURE_PINS.json.xz','NLF_CLOSURE_PINS.json.sha256','NLF_HOST_FINAL.json'];print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in names}}))
''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(t))
print('NLF retained export and complete closure pins collected')
