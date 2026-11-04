from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent;rev='889de8ab372ef3478e76d309a9a7753601344811';path='evidence/slice-d-prepare-20261104/NFW_QueryEntry.lean'
raw=subprocess.check_output(['git','show',rev+':'+path],text=True)
s=raw.replace('import NFW_PowersDomain','import NGC_Initialization').replace('AspisR1.NFW_QueryEntry','AspisR1.NGC_NFW_QueryEntry')
(E/'NGC_NFW_QueryEntry.lean').write_text(s)
pins=[]
for name in ['NFW_HANDOFF.md','NFW_REMAINING.md','NFW_CLOSED.json', 'NFW_QueryEntry.lean']:
 data=subprocess.check_output(['git','show',rev+':evidence/slice-d-prepare-20261104/'+name]);pins.append(dict(revision=rev,path='evidence/slice-d-prepare-20261104/'+name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)))
(E/'NGC_NFW_IMPORT.json').write_text(json.dumps(dict(inputs=pins,copied_module='NGC_NFW_QueryEntry',changes='physical module/namespace prefix; replace unused powers-domain import with coherent initialization import',proof_body_changes=False,credit='MODEL ONLY until focused compile + combined ax2 replay; NFW native initializer and Prepared/prepare association remain OPEN',no_native_reruns=True,no_sibling_worktree_access=True),indent=1)+'\n')
