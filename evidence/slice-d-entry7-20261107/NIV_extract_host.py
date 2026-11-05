from pathlib import Path
import json,hashlib,subprocess,sys
B=Path(__file__).resolve().parent;sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=json.loads((B/'NIV_EXTRACTION_PREFLIGHT.json').read_text());assert p['allowed'] is True and p['status']=='PASS_WARM_PINNED_PREFLIGHT'
assert p['stager_sha256']==sha(B/'NIV_stage.py')
assert not (B/'NIV_EXTRACT_LAUNCHED.json').exists(),'Only ONE extraction authorized'
cmd=['python3','NIV_stage.py','--extract','--function','entry','--workspace',str(B/'NIV_src'),'--out',str(B/'NIV_extracted/entry'),'--opacity',str(B/'NIV_OPACITY.json')]
(B/'NIV_EXTRACT_LAUNCHED.json').write_text(json.dumps(dict(command=cmd,preflight_sha256=sha(B/'NIV_EXTRACTION_PREFLIGHT.json'),stager_sha256=sha(B/'NIV_stage.py'),budget=1,used=1),indent=1)+'\n')
sys.exit(subprocess.run(cmd,cwd=B).returncode)
