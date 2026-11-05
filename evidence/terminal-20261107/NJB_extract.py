from pathlib import Path
import base64,sys,subprocess,shutil
b=Path(__file__).resolve().parent
(b/'NHR_FROZEN_PAYLOAD.json.xz').write_bytes(base64.b64decode((b/'NJB_payload.b64.txt').read_text(),validate=True))
for suffix in ['STAGING_MANIFEST.json','FROZEN_PAYLOAD.json.sha256']:shutil.copyfile(b/('NJB_'+suffix),b/('NHR_'+suffix))
a=['python3','NJB_NHR_stage.py','--workspace',str(b/'NJB_src'),'--out',str(b/'NJB_emitted'),'--opacity',str(b/'NJB_OPACITY.json')]
r=subprocess.run(a+['--check'])
if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run(a+['--extract','--function','NJB_terminal']).returncode)
