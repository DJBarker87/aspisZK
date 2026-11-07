from NNE_formal import *
mods=json.loads((E/'NNE_AUDIT_MODULES.json').read_text())[0]+['NNE_COMBINED_IMPORT']
(E/'NNE_EXPORT_MODULES.json').write_text(json.dumps(mods,indent=1)+'\n')
r=run('NNE_L055','inspect','retention',['python3','NNE_finalize_host.py'],{n:(E/n).read_text() for n in ['NNE_finalize_host.py','NNE_EXPORT_MODULES.json']})
assert r['exit_status']==0
# Preserve exact audit link inputs as source-only artifacts, not binaries.
r=ssh('python3',f'''from pathlib import Path
import json
b=Path({B!r})
print(json.dumps({{n:(b/'NNE_native'/n).read_text() for n in ['NNE_ProofDriver.c','NFA_WALKER.c','NFA_MemoryLimit.c']}}))
''');assert r.returncode==0,r.stderr
idx=json.loads((E/'NNE_INPUTS.json').read_text())
for n,t in json.loads(r.stdout).items():
 raw=t.encode();h=sha(raw);p=E/'NNE_INPUTS'/(h+'.xz')
 if not p.exists():p.write_bytes(lzma.compress(raw))
 idx['objects'][h]=dict(path=str(p.relative_to(E)),bytes=len(raw),archive_sha256=sha(p.read_bytes()))
 idx.setdefault('audit_link_inputs',{})[n]=h
(E/'NNE_INPUTS.json').write_text(json.dumps(idx,indent=1)+'\n')
