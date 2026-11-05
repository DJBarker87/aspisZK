from pathlib import Path
import json,base64
E=Path(__file__).resolve().parent;B='/home/dombarker/project-offloads/codex-cx-terminal-20261107'
# Transport once; committed compressed payload is the evidence source.
(E/'NJB_payload.b64.txt').write_text(base64.b64encode((E/'NJB_FROZEN_PAYLOAD.json.xz').read_bytes()).decode())
(E/'NJB_extract.py').write_text('''from pathlib import Path
import base64,sys,subprocess,shutil
b=Path(__file__).resolve().parent
(b/'NHR_FROZEN_PAYLOAD.json.xz').write_bytes(base64.b64decode((b/'NJB_payload.b64.txt').read_text(),validate=True))
for suffix in ['STAGING_MANIFEST.json','FROZEN_PAYLOAD.json.sha256']:shutil.copyfile(b/('NJB_'+suffix),b/('NHR_'+suffix))
a=['python3','NJB_NHR_stage.py','--workspace',str(b/'NJB_src'),'--out',str(b/'NJB_emitted'),'--opacity',str(b/'NJB_OPACITY.json')]
r=subprocess.run(a+['--check'])
if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run(a+['--extract','--function','NJB_terminal']).returncode)
''')
x=dict(attempt='NJB_E001',kind='extract',module='NJB_terminal',sources=['NJB_extract.py','NJB_NHR_stage.py','NJB_payload.b64.txt','NJB_STAGING_MANIFEST.json','NJB_FROZEN_PAYLOAD.json.sha256','NJB_ROOTS.json','NJB_OPACITY.json'],command=['python3','NJB_extract.py'],timeout=180,env=dict(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=B+'/NJB_target',TMPDIR=B+'/NJB_tmp',CARGO_NET_OFFLINE='true'),deps_fingerprint={},expected_time='Frozen graph validation and optimized Charon compilation followed by one Aeneas translation covering both terminal files',collect_globs=['NJB_emitted/**/*.json','NJB_emitted/raw/**/*.lean'])
(E/'NJB_E001.json').write_text(json.dumps(x,indent=1)+'\n')
print('one extraction configured; source/payload pins retained')
