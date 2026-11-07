from NMS_formal import *
import base64
kind=sys.argv[1] if len(sys.argv)>1 else 'owned'
a={'owned':'NMS_E001','validate':'NMS_E002','stage2':'NMS_E003'}[kind]
files={n:(E/n).read_text() for n in ['NMS_stage.py','NMS_OPACITY.json','NMS_STAGING_MANIFEST.json','NMS_FROZEN_PAYLOAD.json.sha256']}
files['NMS_payload.b64']=base64.b64encode((E/'NMS_FROZEN_PAYLOAD.json.xz').read_bytes()).decode()
files['NMS_extract_host.py']='''from pathlib import Path
import base64,shutil,subprocess,sys
b=Path(__file__).resolve().parent
p=b/'NMS_FROZEN_PAYLOAD.json.xz';p.write_bytes(base64.b64decode((b/'NMS_payload.b64').read_text()))
# Copy build objects read-only; never mutate the original cache.
src=b.parent/'codex-cx-slice-d-entry7-20261107/NIV_NHR_target';dst=b/'NMS_NMS_target'
if not dst.exists():shutil.copytree(src,dst)
r=subprocess.run(['python3','NMS_stage.py','--extract','--function',sys.argv[1],'--workspace',str(b/'NMS_src'),'--out',str(b/('NMS_extract_'+sys.argv[1])),'--opacity',str(b/'NMS_OPACITY.json')]);sys.exit(r.returncode)
'''
r=run(a,'extract',kind,['python3','NMS_extract_host.py',kind],files)
sys.exit(r['exit_status'])
