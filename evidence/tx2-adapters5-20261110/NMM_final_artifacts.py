from NMM_formal import *
import sys,base64
mode,a=sys.argv[1:]
if mode=='pins':
 r=run(a,'cache','NMM_FinalPins',['python3','NMM_pin_host.py'],extra={'NMM_pin_host.py':(E/'NMM_pin_host.py').read_text(),'NMM_SEED_RECHECK.json':(E/'NMM_SEED.json').read_text()})
 assert r['exit_status']==0
 name='NMM_CLOSURE_PINS.json'
elif mode=='export':
 commit=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();mods=json.loads((E/'NMM_SEMANTIC_MODULES.json').read_text())+['NMM_COMBINED_IMPORT']
 cfg=dict(directory='NMM_exports_20261110_'+commit[:12],modules=mods,source_stage_commit=commit)
 r=run(a,'cache','NMM_FinalExport',['python3','NMM_export_host.py'],extra={'NMM_export_host.py':(E/'NMM_export_host.py').read_text(),'NMM_EXPORT_CONFIG.json':json.dumps(cfg)})
 assert r['exit_status']==0
 name='NMM_EXPORT.json'
else:raise ValueError(mode)
r=ssh('python3',f"from pathlib import Path;import base64;print(base64.b64encode(Path({B!r},{name!r}).read_bytes()).decode())");assert r.returncode==0
raw=base64.b64decode(r.stdout);p=E/name
if len(raw)>10_000_000:p.with_name(name+'.xz').write_bytes(lzma.compress(raw));p.with_name(name+'.sha256').write_text(sha(raw)+'\n')
else:p.write_bytes(raw)
print(json.dumps(dict(file=name,bytes=len(raw),sha256=sha(raw))))
